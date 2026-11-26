-- Prove2me | solution 1 for QuarterSumLadder.quartic_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:28.280237+00:00
-- url     : https://prove2.me/submissions/553dffd9-e525-4f41-9699-918d3769fddf

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_eq_of_pow_four_eq_one
public import Theorems.Thm_QuarterSumLadder_unit_apply_pow_four
attribute [local simp] QuarterSumLadder.gi_re
attribute [local simp] QuarterSumLadder.gi_im

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
variable {p : ℕ} [hp : Fact p.Prime]
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
namespace QuarterSumLadder
theorem _root_.solution {a : ZMod p} (ha : a ≠ 0) :
    χ a = 1 ∨ χ a = gi ∨ χ a = -1 ∨ χ a = -gi :=
  eq_of_pow_four_eq_one (by simpa using unit_apply_pow_four χ hχ (Units.mk0 a ha))
end QuarterSumLadder
