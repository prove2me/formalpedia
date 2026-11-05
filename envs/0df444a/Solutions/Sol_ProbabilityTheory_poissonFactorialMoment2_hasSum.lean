-- Prove2me | solution 1 for ProbabilityTheory.poissonFactorialMoment2_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:31:07.656247+00:00
-- url     : https://prove2.me/submissions/9ec797e7-56d5-4a5c-90b7-88194d635073

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

theorem solution (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ((↑n : ℝ) * (↑n - 1)) *
      (poissonMeasure r).real {n}) ((r : ℝ) ^ 2) := by
  have hshift : ∀ n : ℕ,
      (↑(n + 2) : ℝ) * ↑(n + 1) * (poissonMeasure r).real {n + 2} =
        (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
    intro n
    simp only [poissonMeasure_real_singleton, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have h3 : (↑(n + 2) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hnorm : HasSum (fun n ↦ (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using hasSum_one_poissonMeasure r
  apply (hasSum_nat_add_iff' 2).mp
  simp only [sum_range_succ, sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_mul, zero_add, sub_self, mul_zero, sub_zero]
  have key : ∀ n : ℕ, ((↑(n + 2) : ℝ) * (↑(n + 2) - 1)) *
      (poissonMeasure r).real {n + 2} =
      (r : ℝ) ^ 2 * (poissonMeasure r).real {n} := by
    intro n
    have : (↑(n + 2) : ℝ) - 1 = ↑(n + 1) := by push_cast; ring
    rw [this]
    exact hshift n
  simp_rw [key]
  simpa [mul_one] using hnorm.mul_left ((r : ℝ) ^ 2)
