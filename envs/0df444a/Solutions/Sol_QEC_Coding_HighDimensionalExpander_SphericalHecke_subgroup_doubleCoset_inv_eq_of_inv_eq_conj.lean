-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.subgroup_doubleCoset_inv_eq_of_inv_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:21:07.058976+00:00
-- url     : https://prove2.me/submissions/b97a9a35-a3c5-4563-9e1d-7af54e22b9f9

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
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_subgroup_doubleCoset_conj
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
    {G : Type*} [Group G] (K : Subgroup G) {a b p : G}
    (hp : p ∈ K) (hab : a⁻¹ = p * b * p⁻¹) :
    ((K : Set G) * {a} * (K : Set G))⁻¹ =
      (K : Set G) * {b} * (K : Set G) := by
  have hKinv : ((K : Set G))⁻¹ = (K : Set G) := by
    ext x
    simp
  calc
    ((K : Set G) * {a} * (K : Set G))⁻¹ =
        (K : Set G) * {a⁻¹} * (K : Set G) := by
      simp only [mul_inv_rev, Set.inv_singleton, hKinv, mul_assoc]
    _ = (K : Set G) * {p * b * p⁻¹} * (K : Set G) := by rw [hab]
    _ = (K : Set G) * {b} * (K : Set G) :=
      subgroup_doubleCoset_conj K hp
end QEC.Coding.HighDimensionalExpander.SphericalHecke
