-- Prove2me | solution 1 for ProbabilityTheory.LevyKhintchineTriple.exponent_cnd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:18:03.75077+00:00
-- url     : https://prove2.me/submissions/78e83808-6b27-4471-ac72-ac92689fc543

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_cnd_imag_linear
import Theorems.Thm_ProbabilityTheory_cnd_neg_sq
import Theorems.Thm_ProbabilityTheory_IsConditionallyNegativeDefinite_smul_nonneg
import Theorems.Thm_ProbabilityTheory_IsConditionallyNegativeDefinite_add
import Theorems.Thm_ProbabilityTheory_cnd_integral_levyCompensatedIntegrand
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal BigOperators

theorem solution (T : LevyKhintchineTriple) :
    IsConditionallyNegativeDefinite T.exponent := by
  have hDrift := cnd_imag_linear T.drift
  have hGauss := cnd_neg_sq.smul_nonneg
    (show (0 : ℝ) ≤ (T.gaussianVariance : ℝ) / 2 by positivity)
  have hInt := cnd_integral_levyCompensatedIntegrand T.levyMeasure_isLevyMeasure
  have key : T.exponent = fun ξ : ℝ =>
      (((T.drift : ℂ) * ↑ξ * I) + (↑((T.gaussianVariance : ℝ) / 2) : ℂ) * (-((↑ξ : ℂ) ^ 2)))
        + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure := by
    funext ξ
    simp only [LevyKhintchineTriple.exponent]
    push_cast
    ring
  rw [key]
  exact (hDrift.add hGauss).add hInt
