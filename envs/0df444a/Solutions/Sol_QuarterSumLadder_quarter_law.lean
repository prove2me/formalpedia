-- Prove2me | solution 1 for QuarterSumLadder.quarter_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:49.142194+00:00
-- url     : https://prove2.me/submissions/7d4f01a7-b1ae-43b6-8f26-e9354941cd8e

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_two_pow_Q
public import Theorems.Thm_QuarterSumLadder_char_eq_one_iff_pow
public import Theorems.Thm_QuarterSumLadder_neg_one_ne_one_zmod
public import Theorems.Thm_QuarterSumLadder_char_two
public import Theorems.Thm_QuarterSumLadder_hp2_of
public import Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution : χ 2 = (-1) ^ (R χ 1 + R χ 3) := by
  have hp2 := hp2_of hp8
  have h := two_pow_Q hp8 hχ
  have hc := char_eq_one_iff_pow hp8 hχ (two_ne_zero_zmod hp2)
  rcases Nat.even_or_odd (R χ 1 + R χ 3) with he | ho
  · rw [he.neg_one_pow] at h ⊢; exact hc.2 h
  · rw [ho.neg_one_pow] at h ⊢
    rcases char_two hp8 hχ with h2 | h2
    · exfalso; rw [hc.1 h2] at h; exact absurd h.symm (neg_one_ne_one_zmod hp2)
    · exact h2
end QuarterSumLadder
