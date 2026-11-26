-- Prove2me | solution 1 for QuarterSumLadder.eq_of_pow_four_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:34.874488+00:00
-- url     : https://prove2.me/submissions/bbd571ec-12c8-41d3-abd6-e36f59fbb8ff

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_sq

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution {x : GaussianInt} (h : x ^ 4 = 1) :
    x = 1 ∨ x = gi ∨ x = -1 ∨ x = -gi := by
  have e : (x - 1) * (x + 1) * (x - gi) * (x + gi) = 0 := by
    linear_combination (1 - x ^ 2) * gi_sq + h
  rcases mul_eq_zero.1 e with e | e
  · rcases mul_eq_zero.1 e with e | e
    · rcases mul_eq_zero.1 e with e | e
      · exact Or.inl (sub_eq_zero.1 e)
      · exact Or.inr (Or.inr (Or.inl (eq_neg_of_add_eq_zero_left e)))
    · exact Or.inr (Or.inl (sub_eq_zero.1 e))
  · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left e)))
end QuarterSumLadder
