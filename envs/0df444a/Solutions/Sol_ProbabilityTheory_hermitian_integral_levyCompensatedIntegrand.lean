-- Prove2me | solution 1 for ProbabilityTheory.hermitian_integral_levyCompensatedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:33:17.473385+00:00
-- url     : https://prove2.me/submissions/f3f5af23-3ab7-4a49-802e-2fcd137f0b2f

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_ProbabilityTheory_conj_levyCompensatedIntegrand
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Complex ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

theorem solution {ν : Measure ℝ} (ξ : ℝ) :
    ∫ x, levyCompensatedIntegrand (-ξ) x ∂ν =
      starRingEnd ℂ (∫ x, levyCompensatedIntegrand ξ x ∂ν) := by
  calc ∫ x, levyCompensatedIntegrand (-ξ) x ∂ν
      = ∫ x, starRingEnd ℂ (levyCompensatedIntegrand ξ x) ∂ν :=
        integral_congr_ae (ae_of_all ν fun x => (conj_levyCompensatedIntegrand ξ x).symm)
    _ = starRingEnd ℂ (∫ x, levyCompensatedIntegrand ξ x ∂ν) := integral_conj
