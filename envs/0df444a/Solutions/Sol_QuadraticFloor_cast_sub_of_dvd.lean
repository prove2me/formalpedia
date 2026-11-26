-- Prove2me | solution 1 for QuadraticFloor.cast_sub_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:14.254879+00:00
-- url     : https://prove2.me/submissions/dae53240-7f11-42ad-8512-2689231195fb

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {q x : ℕ} (n : ℕ) (hx : x ≤ q) (h : n ∣ q) :
    ((q - x : ℕ) : ZMod n) = -(x : ZMod n) := by
  rw [Nat.cast_sub hx, (ZMod.natCast_eq_zero_iff q n).2 h, zero_sub]
end QuadraticFloor
