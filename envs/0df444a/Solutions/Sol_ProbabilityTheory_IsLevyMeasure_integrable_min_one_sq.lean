-- Prove2me | solution 1 for ProbabilityTheory.IsLevyMeasure.integrable_min_one_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:36:06.962199+00:00
-- url     : https://prove2.me/submissions/4655b61b-a2e9-4914-bfaa-2cc64aa473b1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_lintegral_min_one_sq_lt_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The Lévy measure condition makes the truncated quadratic weight integrable. -/
theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    Integrable (fun x : ℝ => min 1 (x ^ 2)) ν := by
  refine ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have henorm : ∀ x : ℝ, ‖min 1 (x ^ 2)‖ₑ = ENNReal.ofReal (min 1 (x ^ 2)) := fun x =>
    Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg x))
  simp_rw [henorm]
  exact hν.lintegral_min_one_sq_lt_top
