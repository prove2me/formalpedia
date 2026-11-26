-- Prove2me | solution 1 for QuarterSumLadder.quadraticChar_of_char_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:41.3574+00:00
-- url     : https://prove2.me/submissions/5a7a26b1-f26a-4cca-aaac-372717b9a588

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
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) (h : χ x = 1 ∨ χ x = -1) :
    quadraticChar (ZMod p) x = 1 :=
  (quadraticChar_one_iff_isSquare hx).2 ((isSquare_iff_char hχ hx).2 h)
end QuarterSumLadder
