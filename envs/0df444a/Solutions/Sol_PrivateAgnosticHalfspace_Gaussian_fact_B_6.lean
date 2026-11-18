-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.fact_B_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T20:26:13.388824+00:00
-- url     : https://prove2.me/submissions/af87618a-704e-4c0c-b9fa-50347e1ce653

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian

theorem solution (z : ℝ) (y : Bool) :
    (((2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)) : Measure ℝ).real
      {τ | sign (z - τ) ≠ y} ≤ |z - label y| / 2 := by
  rw [measureReal_ennreal_smul_apply]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  cases y with
  | false =>
    have he : {τ : ℝ | sign (z - τ) ≠ false} = Set.Iic z := by
      ext τ
      simp [sign, sub_nonneg]
    rw [he, measureReal_restrict_apply measurableSet_Iic]
    have hsub : Set.Iic z ∩ Set.Icc (-1 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) z := by
      intro x hx
      exact ⟨hx.2.1, hx.1⟩
    have hm := measureReal_mono (μ := volume) hsub (by simp [Real.volume_Icc])
    rw [Real.volume_real_Icc] at hm
    simp only [label, Bool.false_eq_true, ↓reduceIte]
    have ha : max (z - -1) 0 ≤ |z - -1| := max_le (le_abs_self _) (abs_nonneg _)
    nlinarith
  | true =>
    have he : {τ : ℝ | sign (z - τ) ≠ true} = Set.Ioi z := by
      ext τ
      simp [sign, not_le, sub_neg]
    rw [he, measureReal_restrict_apply measurableSet_Ioi]
    have hsub : Set.Ioi z ∩ Set.Icc (-1 : ℝ) 1 ⊆ Set.Icc z (1 : ℝ) := by
      intro x hx
      exact ⟨le_of_lt hx.1, hx.2.2⟩
    have hm := measureReal_mono (μ := volume) hsub (by simp [Real.volume_Icc])
    rw [Real.volume_real_Icc] at hm
    simp only [label, ↓reduceIte]
    have ha : max (1 - z) 0 ≤ |z - 1| := by
      rw [abs_sub_comm]
      exact max_le (le_abs_self _) (abs_nonneg _)
    nlinarith
