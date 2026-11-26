-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.rationalVectorToReal_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:37.555637+00:00
-- url     : https://prove2.me/submissions/6ac583d3-7bd8-4eff-bcc6-cbdfb5b4c353

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {d : ℕ} :
    Function.Injective (rationalVectorToReal (d := d)) :=
  Rat.cast_injective.comp_left
end SumOfSetsInSeveralDimensions
