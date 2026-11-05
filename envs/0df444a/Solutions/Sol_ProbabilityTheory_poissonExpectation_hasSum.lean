-- Prove2me | solution 1 for ProbabilityTheory.poissonExpectation_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:25:54.426256+00:00
-- url     : https://prove2.me/submissions/69675be8-e90f-48e8-81fe-ddbff400f664

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

theorem solution (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ↑n * (poissonMeasure r).real {n}) (r : ℝ) := by
  have hshift : ∀ n : ℕ,
      ↑(n + 1) * (poissonMeasure r).real {n + 1} =
        (r : ℝ) * (poissonMeasure r).real {n} := by
    intro n
    simp only [poissonMeasure_real_singleton, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  have hnormal : HasSum (fun n ↦ (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using hasSum_one_poissonMeasure r
  apply (hasSum_nat_add_iff' 1).mp
  simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  simp_rw [hshift]
  simpa [mul_one] using hnormal.mul_left (r : ℝ)
