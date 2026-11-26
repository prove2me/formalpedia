-- Prove2me | solution 1 for QuarterSumLadder.char_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:16.939216+00:00
-- url     : https://prove2.me/submissions/f8523830-05bc-4f56-b8eb-2af90d5bec21

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_quartic_values


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8
namespace QuarterSumLadder
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : χ x ≠ 0 := by
  rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> decide
end QuarterSumLadder
