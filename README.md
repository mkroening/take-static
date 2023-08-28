# take-static

[![Crates.io](https://img.shields.io/crates/v/take-static)](https://crates.io/crates/take-static)
[![docs.rs](https://img.shields.io/docsrs/take-static)](https://docs.rs/take-static)
[![CI](https://github.com/mkroening/take-static/actions/workflows/ci.yml/badge.svg)](https://github.com/mkroening/take-static/actions/workflows/ci.yml)

This crate provides the [`take_static`] macro to create statics that provide mutable access only once:

```rust
use take_static::{take_static, TakeStatic};

take_static! {
    static NUMBER: usize = 5;
}

assert_eq!(NUMBER.take(), Some(&mut 5));
assert_eq!(NUMBER.take(), None);
```

For API documentation, see the [docs].

[`take_static`]: https://docs.rs/take-static/latest/take_static/macro.take_static.html
[docs]: https://docs.rs/take-static

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
