-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sumsetCardLowerBound_eq_add_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:44.614007+00:00
-- url     : https://prove2.me/submissions/f82a56d9-8001-404e-952c-22b915d28bbd

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
private lemma sum_Icc_one_add_one (f : ℕ → ℕ) (k : ℕ) :
    ∑ t ∈ Icc 1 (k + 1), f t = f 1 + ∑ t ∈ Icc 1 k, f (t + 1) := by
  rw [← add_sum_Ioc_eq_sum_Icc (by grind), ← Icc_add_one_left_eq_Ioc, ← map_add_right_Icc,
    sum_map]
  rfl
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {d m n : ℕ} (hm : 2 ≤ m) :
    sumsetCardLowerBound d m n = sumsetCardLowerBound d (m - 1) (n - 1) + min (d + 1) n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [sumsetCardLowerBound_eq, sumsetCardLowerBound_eq, (by grind : k + 2 - 1 = k + 1),
    (by grind : k + 1 - 1 = k), sum_Icc_one_add_one]
  simp only [Nat.sub_add_eq, Nat.sub_right_comm _ _ 1]
  grind
end SumOfSetsInSeveralDimensions
