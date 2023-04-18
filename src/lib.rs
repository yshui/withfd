//! `withfd` allows passing file descriptors through Unix sockets.
//!
//! This crate provides adapters for `std::os::unix::net::UnixStream` and
//! `tokio::net::UnixStream` (requires the `tokio` feature) that allow passing
//! file descriptors through them.
//!
//! The adapter allows you to keep using the ordinary `Read` and `Write` (or
//! `AsyncRead` and `AsyncWrite` with the `tokio` feature) interfaces. File
//! descriptors are received and stored as you read, This is different from
//! other similar crates like [`passfd`](https://crates.io/crates/passfd)
//! or [`sendfd`](https://crates.io/crates/sendfd). This is to address the
//! problem where, if you use ordinary read on the `UnixStream` when the other
//! end has sent a file descriptor, the file descriptor will be dropped. This
//! adapter ensures there is no file descriptors being lost.
//!
//! # Example
//!
//! Process 1:
//!
//! ```no_run
//! use withfd::WithFdExt;
//! use std::fs::File;
//! use std::os::unix::io::AsFd;
//! use std::os::unix::net::UnixListener;
//!
//! let file = File::open("/etc/passwd").unwrap();
//! let listener = UnixListener::bind("/tmp/test.sock").unwrap();
//! let (stream, _) = listener.accept().unwrap();
//! let mut stream = stream.with_fd();
//! stream.write_with_fd(b"data", &[file.as_fd()]).unwrap();
//! ```
//!
//! Process 2:
//!
//! ```no_run
//! use withfd::WithFdExt;
//! use std::fs::File;
//! use std::io::Read;
//! use std::os::unix::io::FromRawFd;
//! use std::os::unix::net::UnixStream;
//!
//! let stream = UnixStream::connect("/tmp/test.sock").unwrap();
//! let mut stream = stream.with_fd();
//! let mut buf = [0u8; 4];
//! stream.read_exact(&mut buf[..]).unwrap();
//! let fd = stream.take_fds().next().unwrap();
//! let mut file = File::from(fd);
//! let mut buf = String::new();
//! file.read_to_string(&mut buf).unwrap();
//! println!("{}", buf);
//! ```
#![cfg_attr(docsrs, feature(doc_cfg))]

use std::{
    io::{IoSlice, IoSliceMut, Read, Write},
    os::fd::{AsRawFd, BorrowedFd, FromRawFd, OwnedFd, RawFd},
};

use nix::sys::socket::ControlMessageOwned;

/// Adapter for sending data with file descriptors.
///
/// You can create this by using the [`WithFdExt `] trait and calling the
/// `with_fd` method on supported types.
pub struct WithFd<T> {
    inner: T,
    fds:   Vec<OwnedFd>,
    cmsg:  Vec<u8>,
}

pub trait WithFdExt: Sized {
    fn with_fd(self) -> WithFd<Self>;
}

pub const SCM_MAX_FD: usize = 253;

impl Read for WithFd<std::os::unix::net::UnixStream> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.read_with_fd(buf)
    }
}
impl Write for WithFd<std::os::unix::net::UnixStream> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.inner.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }

    fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()> {
        self.inner.write_all(buf)
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> std::io::Result<usize> {
        self.inner.write_vectored(bufs)
    }

    fn write_fmt(&mut self, fmt: std::fmt::Arguments<'_>) -> std::io::Result<()> {
        self.inner.write_fmt(fmt)
    }
}

impl<T: AsRawFd> WithFd<T> {
    fn write_with_fd_impl(&mut self, buf: &[u8], fds: &[BorrowedFd<'_>]) -> std::io::Result<usize> {
        // Safety: BorrowedFd is repr(transparent) over RawFd
        let fds = unsafe { std::slice::from_raw_parts(fds.as_ptr().cast::<RawFd>(), fds.len()) };
        let fd = self.inner.as_raw_fd();
        let cmsg = nix::sys::socket::ControlMessage::ScmRights(fds);
        let sendmsg = nix::sys::socket::sendmsg::<()>(
            fd,
            &[IoSlice::new(buf)],
            &[cmsg],
            nix::sys::socket::MsgFlags::empty(),
            None,
        )?;
        Ok(sendmsg)
    }

    fn read_with_fd(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let fd = self.inner.as_raw_fd();
        let recvmsg = nix::sys::socket::recvmsg::<()>(
            fd,
            &mut [IoSliceMut::new(buf)],
            Some(&mut self.cmsg),
            nix::sys::socket::MsgFlags::empty(),
        )?;
        for cmsg in recvmsg.cmsgs() {
            if let ControlMessageOwned::ScmRights(fds) = cmsg {
                self.fds
                    .extend(fds.iter().map(|&fd| unsafe { OwnedFd::from_raw_fd(fd) }));
            }
        }
        Ok(recvmsg.bytes)
    }

    /// Returns an iterator over the file descriptors received.
    /// Every file descriptor this iterator yields will be removed from the
    /// internal buffer, and will not be returned again. Dropping the iterator
    /// without exhausting it will leave the remaining file descriptors intact.
    pub fn take_fds(&mut self) -> impl Iterator<Item = OwnedFd> + '_ {
        struct Iter<'a>(&'a mut Vec<OwnedFd>);
        impl Iterator for Iter<'_> {
            type Item = OwnedFd;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.pop()
            }
        }
        Iter(&mut self.fds)
    }
}
impl WithFd<std::os::unix::net::UnixStream> {
    /// Write data, with additional pass file descriptors. For most of the unix
    /// systems, file descriptors must be sent along with at least one byte
    /// of data. This is why there is not a `write_fd` method.
    pub fn write_with_fd(&mut self, buf: &[u8], fds: &[BorrowedFd<'_>]) -> std::io::Result<usize> {
        self.write_with_fd_impl(buf, fds)
    }
}

impl WithFdExt for std::os::unix::net::UnixStream {
    fn with_fd(self) -> WithFd<Self> {
        self.into()
    }
}

impl From<std::os::unix::net::UnixStream> for WithFd<std::os::unix::net::UnixStream> {
    fn from(inner: std::os::unix::net::UnixStream) -> Self {
        Self {
            inner,
            fds: Vec::new(),
            cmsg: nix::cmsg_space!([RawFd; SCM_MAX_FD]),
        }
    }
}

#[cfg(test)]
mod test {
    use std::{
        fs::File,
        io::{Read, Seek, Write},
        os::fd::{AsFd, FromRawFd, OwnedFd},
    };

    use cstr::cstr;
    use nix::sys::memfd::MemFdCreateFlag;

    #[test]
    fn test_send_fd() {
        let (a, b) = std::os::unix::net::UnixStream::pair().unwrap();
        let mut a = super::WithFd::from(a);
        let mut b = super::WithFd::from(b);

        let memfd =
            nix::sys::memfd::memfd_create(cstr!("test"), MemFdCreateFlag::MFD_CLOEXEC).unwrap();
        let memfd = unsafe { OwnedFd::from_raw_fd(memfd) };
        let mut memfd: File = memfd.into();
        a.write_with_fd(b"hello", &[memfd.as_fd()]).unwrap();
        let mut buf = [0u8; 5];
        b.read_exact(&mut buf).unwrap();
        assert_eq!(&buf[..], b"hello");
        let fds = b.take_fds().collect::<Vec<_>>();
        assert_eq!(fds.len(), 1);

        let mut memfd2: File = fds.into_iter().next().unwrap().into();

        memfd.write_all(b"Hello").unwrap();
        drop(memfd);

        memfd2.rewind().unwrap();
        memfd2.read_exact(&mut buf).unwrap();
        assert_eq!(&buf[..], b"Hello");
    }

    #[tokio::test]
    async fn test_send_fd_async() {
        use tokio::io::AsyncReadExt;
        let (a, b) = tokio::net::UnixStream::pair().unwrap();
        let mut a = super::WithFd::from(a);
        let mut b = super::WithFd::from(b);

        let memfd =
            nix::sys::memfd::memfd_create(cstr!("test"), MemFdCreateFlag::MFD_CLOEXEC).unwrap();
        let memfd = unsafe { OwnedFd::from_raw_fd(memfd) };
        let mut memfd: File = memfd.into();
        a.write_with_fd(b"hello", &[memfd.as_fd()]).await.unwrap();
        let mut buf = [0u8; 5];
        b.read_exact(&mut buf).await.unwrap();
        assert_eq!(&buf[..], b"hello");
        let fds = b.take_fds().collect::<Vec<_>>();
        assert_eq!(fds.len(), 1);

        let mut memfd2: File = fds.into_iter().next().unwrap().into();

        memfd.write_all(b"Hello").unwrap();
        drop(memfd);

        memfd2.rewind().unwrap();
        memfd2.read_exact(&mut buf).unwrap();
        assert_eq!(&buf[..], b"Hello");
    }
}

#[cfg(any(feature = "tokio", docsrs))]
#[cfg_attr(docsrs, doc(cfg(feature = "tokio")))]
#[doc(hidden)]
pub mod tokio {
    use std::{
        os::fd::{BorrowedFd, RawFd},
        pin::Pin,
        task::ready,
    };

    use tokio::io::{AsyncRead, AsyncWrite};

    use crate::WithFd;

    impl AsyncRead for WithFd<tokio::net::UnixStream> {
        fn poll_read(
            mut self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            buf: &mut tokio::io::ReadBuf<'_>,
        ) -> std::task::Poll<std::io::Result<()>> {
            ready!(self.inner.poll_read_ready(cx))?;
            let unfilled = buf.initialize_unfilled();
            match (*self).read_with_fd(unfilled) {
                Ok(bytes) => {
                    buf.advance(bytes);
                    std::task::Poll::Ready(Ok(()))
                },
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => std::task::Poll::Pending,
                e => std::task::Poll::Ready(e.map(|_| ())),
            }
        }
    }

    impl AsyncWrite for WithFd<tokio::net::UnixStream> {
        fn poll_write(
            mut self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            buf: &[u8],
        ) -> std::task::Poll<Result<usize, std::io::Error>> {
            Pin::new(&mut self.inner).poll_write(cx, buf)
        }

        fn poll_flush(
            mut self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<Result<(), std::io::Error>> {
            Pin::new(&mut self.inner).poll_flush(cx)
        }

        fn poll_shutdown(
            mut self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<Result<(), std::io::Error>> {
            Pin::new(&mut self.inner).poll_shutdown(cx)
        }

        fn poll_write_vectored(
            mut self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
            bufs: &[std::io::IoSlice<'_>],
        ) -> std::task::Poll<Result<usize, std::io::Error>> {
            Pin::new(&mut self.inner).poll_write_vectored(cx, bufs)
        }

        fn is_write_vectored(&self) -> bool {
            self.inner.is_write_vectored()
        }
    }

    impl WithFd<tokio::net::UnixStream> {
        /// Write data, with additional pass file descriptors. For most of the
        /// unix systems, file descriptors must be sent along with at
        /// least one byte of data. This is why there is not a
        /// `write_fd` method.
        pub async fn write_with_fd(
            &mut self,
            buf: &[u8],
            fds: &[BorrowedFd<'_>],
        ) -> std::io::Result<usize> {
            loop {
                self.inner.writable().await?;
                match self.write_with_fd_impl(buf, fds) {
                    Ok(bytes) => break Ok(bytes),
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => continue,
                    e => break Ok(e?),
                }
            }
        }
    }
    impl From<tokio::net::UnixStream> for WithFd<tokio::net::UnixStream> {
        fn from(inner: tokio::net::UnixStream) -> Self {
            Self {
                inner,
                fds: Vec::new(),
                cmsg: nix::cmsg_space!([RawFd; super::SCM_MAX_FD]),
            }
        }
    }
    impl super::WithFdExt for tokio::net::UnixStream {
        fn with_fd(self) -> super::WithFd<Self> {
            self.into()
        }
    }
}
