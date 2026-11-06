-- Prove2me | solution 1 for ProbabilityTheory.smearedMeasure_gaussianVariance_inj
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:45:53.32207+00:00
-- url     : https://prove2.me/submissions/53dded33-0ebe-4f5a-81c0-3031d2d96243

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Theorems.Thm_ProbabilityTheory_smearedMeasure_singleton_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The atom at zero identifies the Gaussian coefficient of a smeared Levy measure. -/
theorem solution {ν₁ ν₂ : Measure ℝ}
    (hν₁ : IsLevyMeasure ν₁) (hν₂ : IsLevyMeasure ν₂) {σ₁ σ₂ : ℝ≥0}
    (h : smearedMeasure σ₁ ν₁ = smearedMeasure σ₂ ν₂) : σ₁ = σ₂ := by
  have h0 : (σ₁ : ℝ≥0∞) / 6 = (σ₂ : ℝ≥0∞) / 6 := by
    have hpt : (smearedMeasure σ₁ ν₁) {(0 : ℝ)} = (smearedMeasure σ₂ ν₂) {(0 : ℝ)} := by rw [h]
    rwa [smearedMeasure_singleton_zero σ₁ hν₁, smearedMeasure_singleton_zero σ₂ hν₂] at hpt
  have h6 : (σ₁ : ℝ≥0∞) / 6 * 6 = (σ₂ : ℝ≥0∞) / 6 * 6 := by rw [h0]
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num),
    ENNReal.div_mul_cancel (by norm_num) (by norm_num)] at h6
  exact ENNReal.coe_inj.mp h6
