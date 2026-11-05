-- Prove2me | solution 1 for ProbabilityTheory.integral_id_poissonMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:44:14.054488+00:00
-- url     : https://prove2.me/submissions/f0fbeee0-64e2-481c-b59d-d247c04564e3

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
    ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  refine (tsum_congr fun n ↦ ?_).trans
    (ProbabilityTheory.poissonExpectation_hasSum r).tsum_eq
  rw [poissonMeasure_real_singleton]
  ring
