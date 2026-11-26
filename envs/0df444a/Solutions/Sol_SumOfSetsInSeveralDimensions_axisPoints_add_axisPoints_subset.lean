-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.axisPoints_add_axisPoints_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:22.693701+00:00
-- url     : https://prove2.me/submissions/7f045f6a-ee59-4187-a5b7-a8ca61b27c3f

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

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {e : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (k l : ℕ) :
    axisPoints e k + axisPoints e l ⊆ axisPoints e (k + l) := by
  intro z hz
  obtain ⟨_, hx, _, hy, rfl⟩ := mem_add.1 hz
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hy
  refine mem_image.2 ⟨i + j, by grind, ?_⟩
  rw [Nat.cast_add, Pi.single_add]
end SumOfSetsInSeveralDimensions
