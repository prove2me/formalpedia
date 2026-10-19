-- Prove2me | solution 1 for QuantumParallelRepetition.sum_positive_difference_eq_totalVariation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/d0f8de79-c100-44cc-8e49-82b7f9ae107e

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    (p q : ι → ℝ)
    (hp : (∑ i, p i) = 1)
    (hq : (∑ i, q i) = 1) :
    (∑ i, max (p i - q i) 0) = finiteTotalVariation p q := by
  classical
  have hpoint (x : ℝ) : max x 0 = (|x| + x) / 2 := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · have hxneg : x < 0 := lt_of_not_ge hx
      rw [max_eq_right hxneg.le, abs_of_neg hxneg]
      ring
  have hzero : (∑ i, (p i - q i)) = 0 := by
    rw [Finset.sum_sub_distrib, hp, hq, sub_self]
  unfold finiteTotalVariation
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hzero, add_zero]
end QuantumParallelRepetition
