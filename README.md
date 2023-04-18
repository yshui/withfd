withfd
------

<!-- cargo-rdme start -->

`withfd` allows passing file descriptors through Unix sockets.

This crate provides adapters for `std::os::unix::net::UnixStream` and
`tokio::net::UnixStream` (requires the `tokio` feature) that allow passing
file descriptors through them.

The adapter allows you to keep using the ordinary `Read` and `Write` (or
`AsyncRead` and `AsyncWrite` with the `tokio` feature) interfaces. File
descriptors are received and stored as you read, This is different from
other similar crates like [`passfd`](https://crates.io/crates/passfd)
or [`sendfd`](https://crates.io/crates/sendfd). This is to address the
problem where, if you use ordinary read on the `UnixStream` when the other
end has sent a file descriptor, the file descriptor will be dropped. This
adapter ensures there is no file descriptors being lost.

### Example

Process 1:

```rust
use withfd::WithFdExt;
use std::fs::File;
use std::os::unix::io::AsFd;
use std::os::unix::net::UnixListener;

let file = File::open("/etc/passwd").unwrap();
let listener = UnixListener::bind("/tmp/test.sock").unwrap();
let (stream, _) = listener.accept().unwrap();
let mut stream = stream.with_fd();
stream.write_with_fd(b"data", &[file.as_fd()]).unwrap();
```

Process 2:

```rust
use withfd::WithFdExt;
use std::fs::File;
use std::io::Read;
use std::os::unix::io::FromRawFd;
use std::os::unix::net::UnixStream;

let stream = UnixStream::connect("/tmp/test.sock").unwrap();
let mut stream = stream.with_fd();
let mut buf = [0u8; 4];
stream.read_exact(&mut buf[..]).unwrap();
let fd = stream.take_fds().next().unwrap();
let mut file = File::from(fd);
let mut buf = String::new();
file.read_to_string(&mut buf).unwrap();
println!("{}", buf);
```

<!-- cargo-rdme end -->
