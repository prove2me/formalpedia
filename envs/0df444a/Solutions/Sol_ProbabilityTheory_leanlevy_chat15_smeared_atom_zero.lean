-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_smeared_atom_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:36:32.971207+00:00
-- url     : https://prove2.me/submissions/007d4744-2cbc-40f4-a3a0-48b104f57724

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

/-- A Dirac atom survives addition of a density whose base measure has no atom. -/
theorem solution (a : ℝ≥0∞) {ν : Measure ℝ} (hν0 : ν {0} = 0)
    (f : ℝ → ℝ≥0∞) :
    (a • Measure.dirac (0 : ℝ) + ν.withDensity f) {0} = a := by
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_singleton 0), mul_one,
    withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ hν0, add_zero]
