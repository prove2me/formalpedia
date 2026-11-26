-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_full_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:08.198392+00:00
-- url     : https://prove2.me/submissions/5bfdbb01-d181-441b-bc54-6f63eff040c4

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq_add_min

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {d m n p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound d (m - 1) (n - 1) ≤ p) (hcard : p + d + 1 ≤ s) :
    sumsetCardLowerBound d m n ≤ s := by
  grind [sumsetCardLowerBound_eq_add_min (d := d) (n := n) hm]
end SumOfSetsInSeveralDimensions
