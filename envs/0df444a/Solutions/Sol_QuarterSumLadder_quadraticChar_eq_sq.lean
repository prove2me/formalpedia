-- Prove2me | solution 1 for QuarterSumLadder.quadraticChar_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:13.021813+00:00
-- url     : https://prove2.me/submissions/f6f792d4-f033-42b7-873b-b9650763fa73

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_sq
public import Theorems.Thm_QuarterSumLadder_quartic_values
public import Theorems.Thm_QuarterSumLadder_quadraticChar_of_char_one
public import Theorems.Thm_QuarterSumLadder_quadraticChar_of_char_gi
attribute [local simp] QuarterSumLadder.gi_re
attribute [local simp] QuarterSumLadder.gi_im

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace QuarterSumLadder
theorem _root_.solution {n : ZMod p} (hn : n ≠ 0) :
    ((quadraticChar (ZMod p) n : ℤ) : GaussianInt) = χ n ^ 2 := by
  rcases quartic_values χ hχ hn with h | h | h | h
  · rw [quadraticChar_of_char_one hχ hn (Or.inl h), h]; simp
  · rw [quadraticChar_of_char_gi hχ hn (Or.inl h), h, gi_sq]; simp
  · rw [quadraticChar_of_char_one hχ hn (Or.inr h), h]; simp
  · rw [quadraticChar_of_char_gi hχ hn (Or.inr h), h, neg_sq, gi_sq]; simp
end QuarterSumLadder
