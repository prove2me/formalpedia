-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.affineDim_axisUnionBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:26.4946+00:00
-- url     : https://prove2.me/submissions/2af014ae-4935-4512-a977-8ac579dae16e

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
public import Theorems.Thm_Finset_affineDim_eq_finrank_vectorSpan
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
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) :
    (axisUnionBasis e k e).affineDim = e + 1 := by
  have h0 : (0 : Fin (e + 1) → ℝ) ∈ axisUnionBasis e k e :=
    mem_union_left _ (mem_image.2 ⟨0, by simp, by simp⟩)
  suffices h : Submodule.span ℝ
      ((· -ᵥ (0 : Fin (e + 1) → ℝ)) '' (axisUnionBasis e k e : Set (Fin (e + 1) → ℝ))) = ⊤ by
    rw [affineDim_eq_finrank_vectorSpan, vectorSpan_eq_span_vsub_set_right ℝ (mem_coe.2 h0),
      h, finrank_top, Module.finrank_fin_fun]
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin (e + 1))).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨Pi.single i 1, ?_, by simp⟩
  induction i using Fin.cases with
  | zero => exact mem_union_left _ (mem_image.2 ⟨1, by grind, by simp⟩)
  | succ j => exact mem_union_right _ (mem_image.2 ⟨j, by simp, rfl⟩)
end SumOfSetsInSeveralDimensions
