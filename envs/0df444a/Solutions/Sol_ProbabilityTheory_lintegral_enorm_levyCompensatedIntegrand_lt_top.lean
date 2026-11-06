-- Prove2me | solution 1 for ProbabilityTheory.lintegral_enorm_levyCompensatedIntegrand_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:33:20.144205+00:00
-- url     : https://prove2.me/submissions/1ed2a450-ab4e-4678-b4c0-6a5d2902a8b9

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_ProbabilityTheory_norm_levyCompensatedIntegrand_le
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Complex ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) (ξ : ℝ) :
    ∫⁻ x, ‖levyCompensatedIntegrand ξ x‖ₑ ∂ν < ⊤ := by
  have hC : (0 : ℝ) ≤ 2 + 3 * ξ ^ 2 := by positivity
  calc ∫⁻ x, ‖levyCompensatedIntegrand ξ x‖ₑ ∂ν
      = ∫⁻ x, ENNReal.ofReal ‖levyCompensatedIntegrand ξ x‖ ∂ν := by
        simp only [ofReal_norm]
    _ ≤ ∫⁻ x, ENNReal.ofReal ((2 + 3 * ξ ^ 2) * min 1 (x ^ 2)) ∂ν := by
        apply lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal (norm_levyCompensatedIntegrand_le ξ x)
    _ = ∫⁻ x, ENNReal.ofReal (2 + 3 * ξ ^ 2) * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        congr 1
        ext x
        rw [← ENNReal.ofReal_mul hC]
    _ = ENNReal.ofReal (2 + 3 * ξ ^ 2) * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ofReal_lt_top hν.2
