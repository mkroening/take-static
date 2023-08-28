//! This crate provides the [`take_static`] macro to create statics that provide mutable access only once:
//!
//! ```
//! use take_static::{take_static, TakeStatic};
//!
//! take_static! {
//!     static NUMBER: usize = 5;
//! }
//!
//! assert_eq!(NUMBER.take(), Some(&mut 5));
//! assert_eq!(NUMBER.take(), None);
//! ```
//!
//! The resulting statics are [`TakeStatic`].

#![no_std]

use core::cell::UnsafeCell;

use call_once::CallOnce;

/// A synchronization primitive which can be accessed only once.
///
/// This type is a thread-safe cell that can only be used in statics.
/// [`TakeStatic::take`] provides a mutable reference to the contents without RAII guards, but only on the first try.
///
/// # Similarities with `takecell::TakeCell`
///
/// `TakeStatic` is similar to [`takecell::TakeCell`] in that both can be used to create singletons.
/// Additionally, `TakeCell`s can be created at runtime, making them suitable for other use-cases such as [doing work only once].
/// `TakeStatic`, on the other hand, is specialized to creating statics through [`take_static`], allowing even `!Send` types to be used and not requiring explicitly naming the wrapper type.
///
/// [`takecell::TakeCell`]: https://docs.rs/takecell/0.1.1/takecell/struct.TakeCell.html
/// [doing work only once]: https://docs.rs/takecell/0.1.1/takecell/index.html#doing-work-only-once
///
/// # Similarities with `cortex_m::singleton`
///
/// `TakeStatic` can be used similarly to [`cortex_m::singleton`] to create a mutable reference to a statically allocated value.
/// In contrast to `cortex_m::singleton`, `TakeStatic` is thread safe.
///
/// [`cortex_m::singleton`]: https://docs.rs/cortex-m/0.7.7/cortex_m/macro.singleton.html
///
/// # Examples
///
/// ```
/// use take_static::{take_static, TakeStatic};
///
/// take_static! {
///     static NUMBER: usize = 5;
/// }
///
/// assert_eq!(NUMBER.take(), Some(&mut 5));
/// assert_eq!(NUMBER.take(), None);
/// ```
#[derive(Debug)]
pub struct TakeStatic<T: ?Sized> {
    taken: CallOnce,
    data: UnsafeCell<T>,
}

// SAFETY: This is safe even without `Send` bound,
// as `TakeStatics` can only ever be constructed at compile-time for statics.
// The consteval “thread” is not considered part of the `Send` contract.
unsafe impl<T: ?Sized> Sync for TakeStatic<T> {}

/// Declare a new static that provides mutable access—but only once.
///
/// # Syntax
///
/// The macro wraps any number of static declarations and makes them [`TakeStatic`].
/// Publicity and attributes for each static are allowed. Example:
///
/// ```
/// use take_static::take_static;
/// take_static! {
///     pub static FOO: u32 = 1;
///
///     static BAR: f32 = 1.0;
/// }
///
/// assert_eq!(FOO.take(), Some(&mut 1));
/// assert_eq!(BAR.take(), Some(&mut 1.0));
/// ```
///
/// See [`TakeStatic`] documentation for more information.
// Modeled after `thread_local` and `lazy_static`.
#[macro_export]
macro_rules! take_static {
    // empty (base case for the recursion)
    () => {};

    // process multiple declarations
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = $init:expr; $($rest:tt)*) => (
        $crate::take_static!($(#[$attr])* $vis static $name: $t = $init);
        $crate::take_static!($($rest)*);
    );

    // handle a single declaration
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = $init:expr) => (
        $(#[$attr])* $vis static $name: $crate::TakeStatic<$t> = {
            const INIT_EXPR: $t = $init;
            // SAFETY: this initializes a static.
            unsafe { $crate::TakeStatic::new(INIT_EXPR) }
        };
    );
}

impl<T> TakeStatic<T> {
    /// Creates a new `TakeStatic` containing the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use take_static::{take_static, TakeStatic};
    ///
    /// static TAKE_STATIC: TakeStatic<usize> = unsafe { TakeStatic::new(5) };
    /// ```
    ///
    /// # Safety
    ///
    /// This function may only be used to initialize a static item.
    /// This is due to the unconditional `Sync` impl of `TakeStatic`.
    #[doc(hidden)]
    #[inline]
    pub const unsafe fn new(val: T) -> Self {
        Self {
            taken: CallOnce::new(),
            data: UnsafeCell::new(val),
        }
    }
}

impl<T: ?Sized> TakeStatic<T> {
    /// Takes the mutable reference to the wrapped value.
    ///
    /// Only the first call returns `Some`.
    /// All subsequent calls return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use take_static::{take_static, TakeStatic};
    ///
    /// take_static! {
    ///     static TAKE_STATIC: usize = 5;
    /// }
    ///
    /// let number = TAKE_STATIC.take().unwrap();
    /// assert_eq!(number, &mut 5);
    /// assert!(TAKE_STATIC.take().is_none());
    /// ```
    #[inline]
    #[must_use]
    pub fn take(&self) -> Option<&mut T> {
        self.taken
            .call_once()
            .ok()
            .map(|_| unsafe { &mut *self.data.get() })
    }

    /// Returns `true` if the mutable reference has been taken.
    ///
    /// # Examples
    ///
    /// ```
    /// use take_static::{take_static, TakeStatic};
    ///
    /// take_static! {
    ///     static TAKE_STATIC: usize = 5;
    /// }
    ///
    /// assert!(!TAKE_STATIC.is_taken());
    /// let number = TAKE_STATIC.take().unwrap();
    /// assert!(TAKE_STATIC.is_taken());
    /// ```
    #[inline]
    pub fn is_taken(&self) -> bool {
        self.taken.was_called()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn visibility() {
        take_static! {
            static SELF: u8 = 3;
        }

        mod module {
            use super::*;

            take_static! {
                static _SELF: u8 = 3;
                pub(super) static SUPER: u8 = 3;
                pub(crate) static CRATE: u8 = 3;
                pub static PUB: u8 = 3;
            }
        }

        assert_eq!(SELF.take(), Some(&mut 3));
        assert_eq!(module::SUPER.take(), Some(&mut 3));
        assert_eq!(module::CRATE.take(), Some(&mut 3));
        assert_eq!(module::PUB.take(), Some(&mut 3));
    }

    #[test]
    fn always_sync() {
        use core::ptr;

        take_static! {
            static FOO: *mut u8 = ptr::null_mut();
        }
        assert_eq!(FOO.take(), Some(&mut ptr::null_mut()));
    }

    #[test]
    fn init_block() {
        take_static! {
            static FOO: u8 = {
                let value = 1 + 2;
                value
            };
        }
        assert_eq!(FOO.take(), Some(&mut 3));
    }

    #[test]
    fn single_declaration() {
        take_static!(static FOO: u8 = 3);
        assert_eq!(FOO.take(), Some(&mut 3));
    }
}
