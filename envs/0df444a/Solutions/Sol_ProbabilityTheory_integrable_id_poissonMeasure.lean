-- Prove2me | solution 1 for ProbabilityTheory.integrable_id_poissonMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:43:40.441212+00:00
-- url     : https://prove2.me/submissions/eb46c2c3-78b7-4b79-82ca-66236e5c614b

import Definitions.Def_LeanLevy_Probability_Poisson
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_LeanLevy_Probability_Characteristic
import Theorems.Thm_ProbabilityTheory_poissonExpectation_hasSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Complex Finset ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem solution (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  refine (ProbabilityTheory.poissonExpectation_hasSum r).summable.congr fun n ↦ ?_
  rw [Real.norm_of_nonneg (Nat.cast_nonneg n),
    poissonMeasure_real_singleton, mul_comm]
