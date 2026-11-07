-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonal_smithDiagonalCoeff_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:04:29.420233+00:00
-- url     : https://prove2.me/submissions/a4521dd5-3e66-4ff8-a2ab-f1400a0a8362

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_smithDiagonalCoeff_eq_unit_mul_X_pow
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
    Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) =
      (smithUnitGeneralLinear (k := k) (d := d) A :
        Matrix (Fin d) (Fin d) (IntegerRing k)) *
      smithPowerDiagonal (k := k) (d := d) A := by
  change Matrix.diagonal (smithDiagonalCoeff (k := k) (d := d) A) =
    (diagonalGeneralLinear (IntegerRing k) d
        (smithCoeffUnit (k := k) (d := d) A) :
      Matrix (Fin d) (Fin d) (IntegerRing k)) *
    Matrix.diagonal
      (fun i => PowerSeries.X ^ smithExponent (k := k) (d := d) A i)
  rw [show (diagonalGeneralLinear (IntegerRing k) d
      (smithCoeffUnit (k := k) (d := d) A) :
        Matrix (Fin d) (Fin d) (IntegerRing k)) =
      Matrix.diagonal fun i =>
        (smithCoeffUnit (k := k) (d := d) A i : IntegerRing k) by
    apply Matrix.ext
    intro i j
    simp [diagonalGeneralLinear_apply, Matrix.diagonal_apply]]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact smithDiagonalCoeff_eq_unit_mul_X_pow (k := k) (d := d) A i
end QEC.Coding.HighDimensionalExpander.SphericalHecke
