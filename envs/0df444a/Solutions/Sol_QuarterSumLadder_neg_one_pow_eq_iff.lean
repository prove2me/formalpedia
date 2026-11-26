-- Prove2me | solution 1 for QuarterSumLadder.neg_one_pow_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:56.328531+00:00
-- url     : https://prove2.me/submissions/daaf986f-5972-483f-b9e2-524a0677b786

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_neg_one_ne_one_zmod
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
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
theorem _root_.solution (hp2 : p ≠ 2) (a b : ℕ) :
    (-1 : ZMod p) ^ a = (-1) ^ b ↔ a % 2 = b % 2 := by
  rw [neg_one_pow_eq_pow_mod_two (R := ZMod p), neg_one_pow_eq_pow_mod_two (R := ZMod p) (n := b)]
  have h1 := neg_one_ne_one_zmod hp2
  have ha := Nat.mod_lt a (show 0 < 2 by norm_num)
  have hb := Nat.mod_lt b (show 0 < 2 by norm_num)
  interval_cases (a % 2) <;> interval_cases (b % 2) <;> simp [h1, h1.symm]
end QuarterSumLadder
