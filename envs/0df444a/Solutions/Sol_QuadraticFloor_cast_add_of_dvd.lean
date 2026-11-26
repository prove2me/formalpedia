-- Prove2me | solution 1 for QuadraticFloor.cast_add_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:27.640154+00:00
-- url     : https://prove2.me/submissions/a33b12df-5a12-4d2d-a9eb-ee6ca63dd9e6

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (x m n : ℕ) (h : n ∣ m) : ((x + m : ℕ) : ZMod n) = x := by
  rw [Nat.cast_add, (ZMod.natCast_eq_zero_iff m n).2 h, add_zero]
end QuadraticFloor
