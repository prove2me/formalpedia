-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.disjoint_axisPoints_unitVectors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:16.63081+00:00
-- url     : https://prove2.me/submissions/e3d40cb0-bb9d-415c-8bcc-8a2060d4e48e

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
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset



set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {e : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (k c : ℕ) :
    Disjoint (axisPoints e k) (unitVectors e c) := by
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨i, -, rfl⟩ := mem_image.1 hx
  obtain ⟨j, -, h⟩ := mem_image.1 hx'
  simpa using congr_fun h j.succ
end SumOfSetsInSeveralDimensions
