-- Prove2me | solution 1 for QuarterSumLadder.quartic_apply_neg_one_of_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:54.199709+00:00
-- url     : https://prove2.me/submissions/485b3484-0be4-4a11-b0da-61bbd65a5438

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_pm_gi_pow_two_mul
public import Theorems.Thm_QuarterSumLadder_exists_generator
public import Theorems.Thm_QuarterSumLadder_quartic_apply_generator
public import Theorems.Thm_QuarterSumLadder_neg_one_eq_generator_pow
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
theorem _root_.solution (hp8 : p % 8 = 1) : χ (-1) = 1 := by
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  have hp2 : p ≠ 2 := by omega
  rw [← neg_one_eq_generator_pow hp2 hgo, Units.val_pow_eq_pow_val, map_pow,
    show (p - 1) / 2 = 2 * (2 * (p / 8)) by omega,
    pm_gi_pow_two_mul (quartic_apply_generator χ hχ hg)]
  simp [pow_mul]
end QuarterSumLadder
