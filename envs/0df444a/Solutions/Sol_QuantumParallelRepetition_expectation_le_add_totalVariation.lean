-- Prove2me | solution 1 for QuantumParallelRepetition.expectation_le_add_totalVariation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/e34237cf-741d-4396-82a5-d84afc021880

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_sum_positive_difference_eq_totalVariation

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
namespace QuantumParallelRepetition
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (p q f : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1)
    (U : ℝ)
    (hfzero : ∀ i, 0 ≤ f i)
    (hfupper : ∀ i, f i ≤ U) :
    (∑ i, p i * f i) ≤
      (∑ i, q i * f i) + U * finiteTotalVariation p q := by
  classical
  have hterm (i : ι) :
      (p i - q i) * f i ≤ U * max (p i - q i) 0 := by
    by_cases hi : 0 ≤ p i - q i
    · rw [max_eq_left hi]
      nlinarith [mul_nonneg hi (sub_nonneg.mpr (hfupper i))]
    · have hineg : p i - q i < 0 := lt_of_not_ge hi
      rw [max_eq_right hineg.le]
      simp only [mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hineg.le (hfzero i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hpositive := sum_positive_difference_eq_totalVariation p q hp hq
  calc
    (∑ i, p i * f i) =
        (∑ i, q i * f i) + ∑ i, (p i - q i) * f i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ (∑ i, q i * f i) +
          ∑ i, U * max (p i - q i) 0 := by
      linarith
    _ = (∑ i, q i * f i) +
          U * finiteTotalVariation p q := by
      rw [← Finset.mul_sum, hpositive]
end QuantumParallelRepetition
