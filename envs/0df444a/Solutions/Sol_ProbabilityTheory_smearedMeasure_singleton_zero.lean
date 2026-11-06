-- Prove2me | solution 1 for ProbabilityTheory.smearedMeasure_singleton_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:28:08.215201+00:00
-- url     : https://prove2.me/submissions/4be9b59c-dc03-4281-8aff-3987c6433c62

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The Levy measure's zero atom vanishes in the smeared density term. -/
theorem solution (σ_sq : ℝ≥0) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    smearedMeasure σ_sq ν {0} = (σ_sq : ℝ≥0∞) / 6 := by
  have hd : (Measure.dirac (0 : ℝ)) {0} = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton 0)
  rw [smearedMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hd, mul_one,
    withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ hν.1, add_zero]
