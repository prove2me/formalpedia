-- Prove2me | solution 1 for QuadraticFloor.cast8_add_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:01.873326+00:00
-- url     : https://prove2.me/submissions/d4576427-d286-4fbe-ae67-2a21867c333d

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {A p : ℕ} (hAp : Odd (A * p)) (x : ℕ) :
    ((x + 4 * A * p : ℕ) : ZMod 8) = (x : ZMod 8) + 4 := by
  have h1 : (A * p) % 2 = 1 := Nat.odd_iff.1 hAp
  have hm : (4 * A * p) % 8 = 4 % 8 := by rw [show 4 * A * p = 4 * (A * p) by ring]; omega
  have h4 : ((4 * A * p : ℕ) : ZMod 8) = 4 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ 8).2 hm
    rw [Nat.cast_ofNat] at this
    exact this
  rw [Nat.cast_add, h4]
end QuadraticFloor
