-- Prove2me | solution 1 for ProbabilityTheory.smearedMeasure_inj
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:56:54.164059+00:00
-- url     : https://prove2.me/submissions/59dba98d-a6e9-4c28-a3b6-c58e4b7a468b

import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Theorems.Thm_ProbabilityTheory_smearedMeasure_gaussianVariance_inj
import Theorems.Thm_ProbabilityTheory_smearedMeasure_levyMeasure_inj

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Source-exact reconstruction of the smeared Lévy-triple injectivity pair. -/
theorem solution :
    ∀ {ν₁ ν₂ : Measure ℝ}, IsLevyMeasure ν₁ → IsLevyMeasure ν₂ →
      ∀ {σ₁ σ₂ : ℝ≥0}, smearedMeasure σ₁ ν₁ = smearedMeasure σ₂ ν₂ →
        σ₁ = σ₂ ∧ ν₁ = ν₂ := by
  intro ν₁ ν₂ hν₁ hν₂ σ₁ σ₂ h
  exact ⟨smearedMeasure_gaussianVariance_inj hν₁ hν₂ h,
    smearedMeasure_levyMeasure_inj hν₁ hν₂ h⟩
