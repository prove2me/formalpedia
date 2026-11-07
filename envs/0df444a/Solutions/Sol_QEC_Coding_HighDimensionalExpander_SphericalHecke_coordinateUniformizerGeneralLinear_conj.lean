-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.coordinateUniformizerGeneralLinear_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:03:56.024645+00:00
-- url     : https://prove2.me/submissions/f6a79482-39a6-425d-9c97-4e907fe82b82

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_permutationGeneralLinear_conj_diagonal
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
    (k : Type u) [Field k] {d : ℕ} (i j : Fin d) :
    permutationGeneralLinear (LocalFunctionField k) (Equiv.swap i j) *
        coordinateUniformizerGeneralLinear k d i *
        permutationGeneralLinear (LocalFunctionField k) (Equiv.swap i j)⁻¹ =
      coordinateUniformizerGeneralLinear k d j := by
  change
    permutationGeneralLinear (LocalFunctionField k) (Equiv.swap i j) *
        diagonalGeneralLinear (LocalFunctionField k) d
          (coordinateUniformizerUnits k d i) *
        (permutationGeneralLinear
          (LocalFunctionField k) (Equiv.swap i j))⁻¹ =
      diagonalGeneralLinear (LocalFunctionField k) d
        (coordinateUniformizerUnits k d j)
  rw [permutationGeneralLinear_conj_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  by_cases hab : a = b
  · subst b
    simp [coordinateUniformizerUnits, diagonalGeneralLinear_apply,
      Function.comp_def, Equiv.swap_apply_eq_iff]
  · simp [hab, diagonalGeneralLinear_apply]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
