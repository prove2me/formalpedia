-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_axisUnionBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:52.474549+00:00
-- url     : https://prove2.me/submissions/9a2286d5-8c3b-426e-ab9c-aa65b19ce19a

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundValues
public import Definitions.Def_SumOfSetsInSeveralDimensions_Construction
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_axisPoints
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_unitVectors
public import Theorems.Thm_SumOfSetsInSeveralDimensions_disjoint_axisPoints_unitVectors

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {e : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (k : ℕ) {c : ℕ} (hc : c ≤ e) : #(axisUnionBasis e k c) = k + 1 + c := by
  rw [axisUnionBasis, card_union_of_disjoint (disjoint_axisPoints_unitVectors k c),
    card_axisPoints, card_unitVectors hc]
end SumOfSetsInSeveralDimensions
