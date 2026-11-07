-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.scalar_mul_fundamentalDiagonal_rankThree_one_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:11:56.926245+00:00
-- url     : https://prove2.me/submissions/7b81a00b-4798-489d-b196-326b20d9783b

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
    (k : Type u) [Field k] :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (uniformizerUnit k) *
        (fundamentalDiagonal k 3 1)⁻¹ =
      permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
        fundamentalDiagonal k 3 2 *
        (permutationGeneralLinear
          (LocalFunctionField k) Fin.revPerm)⁻¹ := by
  change _ = permutationGeneralLinear (LocalFunctionField k) Fin.revPerm *
    diagonalGeneralLinear (LocalFunctionField k) 3
      (fundamentalDiagonalUnits k 3 2) *
    (permutationGeneralLinear (LocalFunctionField k) Fin.revPerm)⁻¹
  rw [permutationGeneralLinear_conj_diagonal]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalDiagonal, fundamentalDiagonalUnits,
      diagonalGeneralLinear_inv, diagonalGeneralLinear_apply, Matrix.mul_apply]
end QEC.Coding.HighDimensionalExpander.SphericalHecke
