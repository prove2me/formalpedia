-- Prove2me | solution 1 for QuarterSumLadder.neg_half_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:27.78025+00:00
-- url     : https://prove2.me/submissions/9bedacc4-48f1-4f68-b682-ea67f1b84614

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_P2M_QuarterSumLadder_val_neg_of_ne_zero__948b4628a7e3
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_odd_p
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) :
    (Odd (-x).val ↔ ¬ Odd x.val) := by
  rw [val_neg_of_ne_zero' hx, Nat.odd_sub (ZMod.val_lt x).le]
  have := odd_p hp2
  simp [this]
end QuarterSumLadder
