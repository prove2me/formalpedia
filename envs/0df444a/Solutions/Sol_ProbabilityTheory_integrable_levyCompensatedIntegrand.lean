-- Prove2me | solution 1 for ProbabilityTheory.integrable_levyCompensatedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:36:07.259901+00:00
-- url     : https://prove2.me/submissions/2339e3c1-0da1-4922-b527-e1f3f39e3d82

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_ProbabilityTheory_measurable_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_lintegral_enorm_levyCompensatedIntegrand_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Complex ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) (ξ : ℝ) :
    Integrable (levyCompensatedIntegrand ξ) ν := by
  exact ⟨(measurable_levyCompensatedIntegrand ξ).aestronglyMeasurable,
    lintegral_enorm_levyCompensatedIntegrand_lt_top hν ξ⟩
