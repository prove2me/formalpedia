-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.clearedMatrix_smith_coordinate_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:24.907074+00:00
-- url     : https://prove2.me/submissions/c26e0f90-76e4-4f0b-a40d-9a3c6efc56de

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_clearedMatrix_apply_smithDomainBasis
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
    {k : Type u} [Field k] {d : ℕ}
    (A : GL (Fin d) (LocalFunctionField k)) :
    LinearMap.toMatrix
        (smithDomainBasis (k := k) (d := d) A)
        (smithAmbientBasis (k := k) (d := d) A)
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).mulVecLin =
      Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) := by
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix_apply]
  change (smithAmbientBasis (k := k) (d := d) A).repr
      (Matrix.mulVec
        (clearedPowerSeriesMatrix (k := k) (d := d)
          (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)))
        (smithDomainBasis (k := k) (d := d) A j)) i = _
  rw [clearedMatrix_apply_smithDomainBasis (k := k) (d := d) A j]
  by_cases h : i = j <;> simp [h]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
