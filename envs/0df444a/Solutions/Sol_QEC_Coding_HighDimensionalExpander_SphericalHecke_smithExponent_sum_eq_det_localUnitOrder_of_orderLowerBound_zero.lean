-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.smithExponent_sum_eq_det_localUnitOrder_of_orderLowerBound_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:07:43.134611+00:00
-- url     : https://prove2.me/submissions/41f61a5c-c90e-43fb-a9c4-0f8ec96971cc

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_matrixClearingScalar_mul_eq_localCartanFactors
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_matrixClearingExponent_eq_zero_of_orderLowerBound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_localUnitOrder_mul
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_powerSeriesGeneralLinear_det_localUnitOrder_eq_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithPowerGeneralLinearLocal_det_localUnitOrder
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
    (A : GL (Fin d) (LocalFunctionField k))
    (hA : MatrixOrderLowerBound 0
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) :
    (∑ i, (smithExponent (k := k) (d := d) A i : ℤ)) =
      localUnitOrder (Matrix.GeneralLinearGroup.det A) := by
  have hclear : matrixClearingExponent
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) = 0 :=
    matrixClearingExponent_eq_zero_of_orderLowerBound_zero _ hA
  have hdet := congrArg Matrix.GeneralLinearGroup.det
    (matrixClearingScalar_mul_eq_localCartanFactors
      (k := k) (d := d) A)
  have horder := congrArg localUnitOrder hdet
  simpa [map_mul, Matrix.GeneralLinearGroup.det_scalar,
    matrixClearingScalarUnit, hclear, localUnitOrder_mul,
    localUnitOrder_inv,
    smithLeftGeneralLinearLocal, smithRightGeneralLinearLocal,
    powerSeriesGeneralLinear_det_localUnitOrder_eq_zero,
    smithPowerGeneralLinearLocal_det_localUnitOrder] using horder.symm
end QEC.Coding.HighDimensionalExpander.SphericalHecke
