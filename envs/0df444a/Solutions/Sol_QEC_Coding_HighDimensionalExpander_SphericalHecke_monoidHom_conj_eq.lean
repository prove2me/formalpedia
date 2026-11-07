-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.monoidHom_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:00.744166+00:00
-- url     : https://prove2.me/submissions/61408911-6c11-4487-bd34-ae95752df937

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped LocalTopology MatrixGroups Pointwise Valued
open Module
universe u
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    {G M : Type*} [Group G] [CommMonoid M] (χ : G →* M) (x g : G) :
    χ (x * g * x⁻¹) = χ g := by
  calc
    χ (x * g * x⁻¹) = χ x * χ g * χ x⁻¹ := by simp only [map_mul]
    _ = χ g * (χ x * χ x⁻¹) := by ac_rfl
    _ = χ g * χ (x * x⁻¹) := by rw [map_mul]
    _ = χ g := by simp
end QEC.Coding.HighDimensionalExpander.SphericalHecke
