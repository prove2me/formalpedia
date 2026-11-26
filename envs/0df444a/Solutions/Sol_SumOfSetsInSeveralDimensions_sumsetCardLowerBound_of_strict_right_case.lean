-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_strict_right_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:54.774818+00:00
-- url     : https://prove2.me/submissions/58a5d72b-4182-44fd-aea2-309252efb298

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq
section
@[expose] public section
namespace SumOfSetsInSeveralDimensions
open Finset
private lemma sum_min_le_sum_min_sub_one_add (d n k : ℕ) :
    ∑ t ∈ Icc 1 k, min d (n - t) ≤ ∑ t ∈ Icc 1 k, min (d - 1) (n - 1 - t) + k := by
  refine (sum_le_sum (g := fun t ↦ min (d - 1) (n - 1 - t) + 1) ?_).trans ?_
  · grind
  · rw [sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, mul_one, Nat.add_sub_cancel]
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {d m n p s : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (hrec : sumsetCardLowerBound (d - 1) m (n - 1) ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  rw [sumsetCardLowerBound_eq] at hrec ⊢
  grind [sum_min_le_sum_min_sub_one_add d n (m - 1)]
end SumOfSetsInSeveralDimensions
