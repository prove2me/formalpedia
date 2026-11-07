-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.subgroup_doubleCoset_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:20:13.821455+00:00
-- url     : https://prove2.me/submissions/446ccf38-42ee-4f20-a259-71c4fac6e920

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply


attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {G : Type*} [Group G] (K : Subgroup G) {b p : G} (hp : p ∈ K) :
    (K : Set G) * {p * b * p⁻¹} * (K : Set G) =
      (K : Set G) * {b} * (K : Set G) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, ⟨l, hl, c, hc, rfl⟩, r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hc
    subst c
    refine ⟨(l * p) * b, ?_, p⁻¹ * r,
      K.mul_mem (K.inv_mem hp) hr, ?_⟩
    · exact ⟨l * p, K.mul_mem hl hp, b, Set.mem_singleton b, rfl⟩
    · simp only [mul_assoc]
  · intro hx
    rcases hx with ⟨y, ⟨l, hl, c, hc, rfl⟩, r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hc
    subst c
    refine ⟨(l * p⁻¹) * (p * b * p⁻¹), ?_, p * r,
      K.mul_mem hp hr, ?_⟩
    · exact ⟨l * p⁻¹, K.mul_mem hl (K.inv_mem hp),
        p * b * p⁻¹, Set.mem_singleton _, rfl⟩
    · simp only [mul_assoc, inv_mul_cancel_left]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
