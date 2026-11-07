-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.det_one_sub_inv_of_charpoly_eq_X_pow_sub_C_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:51.473945+00:00
-- url     : https://prove2.me/submissions/36f1ef5c-17af-4d0e-b52f-2cd8c24bd54c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    {K : Type*} [Field K] (r : Rank)
    (z : Matrix.GeneralLinearGroup (Fin r.matrixRank) K) (y : K)
    (hchar : (z : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K).charpoly =
      Polynomial.X ^ r.matrixRank - Polynomial.C (1 + y)) :
    Matrix.det
        ((1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K) -
          ((z⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank) K) :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) K)) =
      y / (1 + y) := by
  let Z : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K := z
  let Zi : Matrix (Fin r.matrixRank) (Fin r.matrixRank) K :=
    (z⁻¹ : Matrix.GeneralLinearGroup (Fin r.matrixRank) K)
  have hZiZ : Zi * Z = 1 := by
    dsimp [Zi, Z]
    exact congrArg Units.val (inv_mul_cancel z)
  have hfactor : 1 - Zi = Zi * (Z - 1) := by
    rw [mul_sub, hZiZ, mul_one]
  have hdetZ : Matrix.det Z =
      (-1 : K) ^ r.matrixRank * (-(1 + y)) := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hchar]
    cases r <;> norm_num [Rank.matrixRank]
  have hdetOneSubZ : Matrix.det (1 - Z) = -y := by
    have h := Matrix.eval_charpoly Z 1
    rw [hchar] at h
    have hscalar :
        Matrix.scalar (Fin r.matrixRank) (1 : K) = 1 := by
      ext i j
      simp [Matrix.scalar_apply]
    rw [← hscalar]
    calc
      Matrix.det (Matrix.scalar (Fin r.matrixRank) 1 - Z) =
          (Polynomial.X ^ r.matrixRank -
            Polynomial.C (1 + y)).eval 1 := h.symm
      _ = -y := by simp
  have hdetZSubOne : Matrix.det (Z - 1) =
      (-1 : K) ^ r.matrixRank * (-y) := by
    have heq : Z - 1 = -(1 - Z) := (neg_sub 1 Z).symm
    rw [heq, Matrix.det_neg, Fintype.card_fin, hdetOneSubZ]
  have hdetZi : Matrix.det Zi = (Matrix.det Z)⁻¹ := by
    simp [Zi, Z]
  have hdetZne : Matrix.det Z ≠ 0 := by
    dsimp [Z]
    exact Units.ne_zero (Matrix.GeneralLinearGroup.det z)
  have honeaddy : 1 + y ≠ 0 := by
    intro h
    apply hdetZne
    rw [hdetZ, h]
    simp
  rw [hfactor, Matrix.det_mul, hdetZi, hdetZSubOne]
  field_simp [hdetZne, honeaddy]
  rw [hdetZ]
  cases r <;> norm_num [Rank.matrixRank] <;> ring
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
