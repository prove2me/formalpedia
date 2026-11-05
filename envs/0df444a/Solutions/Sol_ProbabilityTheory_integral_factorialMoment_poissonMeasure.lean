-- Prove2me | solution 1 for ProbabilityTheory.integral_factorialMoment_poissonMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:49:43.535658+00:00
-- url     : https://prove2.me/submissions/f69c68a8-7181-4a56-b4ea-dc5703e1131c

import Definitions.Def_LeanLevy_Probability_Poisson
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_LeanLevy_Probability_Characteristic
import Theorems.Thm_ProbabilityTheory_poissonFactorialMoment2_hasSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Complex Finset ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem solution (r : ℝ≥0) :
    ∫ n, ((n : ℝ) * ((n : ℝ) - 1)) ∂(poissonMeasure r) = (r : ℝ) ^ 2 := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  refine (tsum_congr fun n ↦ ?_).trans
    (ProbabilityTheory.poissonFactorialMoment2_hasSum r).tsum_eq
  rw [poissonMeasure_real_singleton]
  ring
