-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.projective_eq_localCartanFactors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:07:37.572118+00:00
-- url     : https://prove2.me/submissions/ab88217b-8537-4ed5-853c-567b90f07ff4

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
    Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk
          (smithLeftGeneralLinearLocal (k := k) (d := d) A) *
        smithPowerCoweight (k := k) (d := d) A *
      (Matrix.ProjGenLinGroup.mk
        (smithRightGeneralLinearLocal (k := k) (d := d) A))⁻¹ := by
  have h := congrArg Matrix.ProjGenLinGroup.mk
    (matrixClearingScalar_mul_eq_localCartanFactors (k := k) (d := d) A)
  simpa only [map_mul, map_inv, Matrix.ProjGenLinGroup.mk_scalar, one_mul,
    smithPowerCoweight] using h
end QEC.Coding.HighDimensionalExpander.SphericalHecke
