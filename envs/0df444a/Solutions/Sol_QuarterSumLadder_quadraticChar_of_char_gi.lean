-- Prove2me | solution 1 for QuarterSumLadder.quadraticChar_of_char_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:51.860246+00:00
-- url     : https://prove2.me/submissions/575e395f-fd6f-41bd-8211-ac5ae1cba442

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_isSquare_iff_char

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
namespace QuarterSumLadder
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) (h : χ x = gi ∨ χ x = -gi) :
    quadraticChar (ZMod p) x = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, isSquare_iff_char hχ hx]
  rintro (h' | h') <;> rcases h with h | h <;> rw [h] at h' <;> revert h' <;> decide
end QuarterSumLadder
