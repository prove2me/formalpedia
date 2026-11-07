-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.matrixClearingScalar_mul_eq_localCartanFactors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:06:40.869104+00:00
-- url     : https://prove2.me/submissions/449b873f-7cd5-448a-8fa0-7465cb74c8b8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_clearedPowerSeriesMatrix_power_factorization
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_powerSeriesGeneralLinearToLocal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_map_smithPowerDiagonal
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_map_inv_smithDomainGeneralLinear

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
    Matrix.GeneralLinearGroup.scalar (Fin d)
        (matrixClearingScalarUnit (k := k) (d := d) A) * A =
      smithLeftGeneralLinearLocal (k := k) (d := d) A *
        smithPowerGeneralLinearLocal (k := k) (d := d) A *
      (smithRightGeneralLinearLocal (k := k) (d := d) A)⁻¹ := by
  apply Units.ext
  change Matrix.scalar (Fin d)
        (matrixClearingScalarUnit (k := k) (d := d) A : LocalFunctionField k) *
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  change (uniformizerUnit k : LocalFunctionField k) ^
      matrixClearingExponent
        (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) •
      (A : Matrix (Fin d) (Fin d) (LocalFunctionField k)) = _
  calc
    _ = (integerEmbedding k).mapMatrix
          (clearedPowerSeriesMatrix (k := k) (d := d)
            (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))) :=
      (map_clearedPowerSeriesMatrix (k := k) (d := d)
        (A : Matrix (Fin d) (Fin d) (LocalFunctionField k))).symm
    _ = (integerEmbedding k).mapMatrix
          ((smithLeftGeneralLinear (k := k) (d := d) A :
              Matrix (Fin d) (Fin d) (IntegerRing k)) *
            smithPowerDiagonal (k := k) (d := d) A *
          (((smithDomainGeneralLinear (k := k) (d := d) A)⁻¹ :
              GL (Fin d) (IntegerRing k)) :
                Matrix (Fin d) (Fin d) (IntegerRing k))) :=
      congrArg (integerEmbedding k).mapMatrix
        (clearedPowerSeriesMatrix_power_factorization (k := k) (d := d) A)
    _ = _ := by
      rw [map_mul, map_mul, ← coe_powerSeriesGeneralLinearToLocal,
        map_smithPowerDiagonal (k := k) (d := d) A,
        map_inv_smithDomainGeneralLinear (k := k) (d := d) A]
      rfl
end QEC.Coding.HighDimensionalExpander.SphericalHecke
