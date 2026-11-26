-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_large_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:47.083209+00:00
-- url     : https://prove2.me/submissions/f5ea0f3e-0155-4e88-83fe-4736b73e14f6

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
private lemma sumsetCardLowerBound_le_large_deletion {d m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    sumsetCardLowerBound d m n ≤ n + sumsetCardLowerBound (d - 1) (m - 1) (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, (by grind : k + 2 - 1 = k + 1),
    (by grind : k + 1 - 1 = k), sum_Icc_succ_top (by grind)]
  grind [sum_min_le_sum_min_sub_one_add d n k]
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {d m n p s : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) (n - 1) ≤ p) (hcard : n + p ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  grind [sumsetCardLowerBound_le_large_deletion (d := d) hm hmn]
end SumOfSetsInSeveralDimensions
