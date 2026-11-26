-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sumsetCardLowerBound_of_equal_right_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:51.185543+00:00
-- url     : https://prove2.me/submissions/197a5be1-a8e9-4f89-bd76-3b823548a35e

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_of_small_case

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {d m p s : ℕ} (hm : 2 ≤ m)
    (hrec : sumsetCardLowerBound (d - 1) (m - 1) m ≤ p) (hcard : m + p ≤ s) :
    sumsetCardLowerBound d m m ≤ s :=
  sumsetCardLowerBound_of_small_case hm le_rfl hrec hcard
end SumOfSetsInSeveralDimensions
