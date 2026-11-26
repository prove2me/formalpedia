-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sumsetCardLowerBound_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:32.352536+00:00
-- url     : https://prove2.me/submissions/dd242f15-5a53-4c0e-a045-b3f26f96d8ce

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (d m n : ℕ) :
    sumsetCardLowerBound d m n = n + ∑ t ∈ Icc 1 (m - 1), min d (n - t) := by
  rfl
end SumOfSetsInSeveralDimensions
