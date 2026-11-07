-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_smeared_restrict_compl
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:36:37.018708+00:00
-- url     : https://prove2.me/submissions/14fafe81-baef-4e59-b608-f0281a1c5dc1

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

/-- Restriction away from zero eliminates a Dirac atom and retains the density. -/
theorem solution (a : ℝ≥0∞) {ν : Measure ℝ} (hν0 : ν {0} = 0)
    (f : ℝ → ℝ≥0∞) :
    (a • Measure.dirac (0 : ℝ) + ν.withDensity f).restrict ({(0 : ℝ)}ᶜ)
      = ν.withDensity f := by
  classical
  rw [Measure.restrict_add, Measure.restrict_smul, restrict_dirac,
    if_neg (by simp), smul_zero, zero_add]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff, show {x : ℝ | x ∉ {(0 : ℝ)}ᶜ} = {(0 : ℝ)} from by
    ext x; simp]
  rw [withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ hν0]
