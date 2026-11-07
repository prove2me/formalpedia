-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicBMatrix_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:42:12.719404+00:00
-- url     : https://prove2.me/submissions/1a9bc6a3-a224-41da-93cc-4b449295589c

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


section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
private theorem det_bThree {K : Type*} [Field K]
    (y : K) (hy : 1 + y ≠ 0) :
    Matrix.det
        (1 - !![0, 1, 0; 0, 0, 1; (1 + y)⁻¹, 0, 0] :
          Matrix (Fin 3) (Fin 3) K) =
      y / (1 + y) := by
  rw [Matrix.det_fin_three]
  simp
  field_simp [hy]
  ring
private theorem det_bFour {K : Type*} [Field K]
    (y : K) (hy : 1 + y ≠ 0) :
    Matrix.det
        (1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
          (1 + y)⁻¹, 0, 0, 0] : Matrix (Fin 4) (Fin 4) K) =
      y / (1 + y) := by
  let B : Matrix (Fin 4) (Fin 4) K :=
    1 - !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1;
      (1 + y)⁻¹, 0, 0, 0]
  change Matrix.det B = _
  have hminor0Matrix :
      B.submatrix Fin.succ (0 : Fin 4).succAbove =
        !![1, -1, 0; 0, 1, -1; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B]
  have hminor0 : Matrix.det
      (B.submatrix Fin.succ (0 : Fin 4).succAbove) = 1 := by
    rw [hminor0Matrix, Matrix.det_fin_three]
    simp
  have hminor1Matrix :
      B.submatrix Fin.succ (1 : Fin 4).succAbove =
        !![0, -1, 0; 0, 1, -1; -(1 + y)⁻¹, 0, 1] := by
    have hlast : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, hlast]
  have hminor1 : Matrix.det
      (B.submatrix Fin.succ (1 : Fin 4).succAbove) =
        -(1 + y)⁻¹ := by
    rw [hminor1Matrix, Matrix.det_fin_three]
    simp
  have hB00 : B 0 0 = 1 := by simp [B]
  have hB01 : B 0 1 = -1 := by simp [B]
  have hB02 : B 0 2 = 0 := by simp [B]
  have hB03 : B 0 3 = 0 := by simp [B]
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_four]
  rw [hB00, hB01, hB02, hB03, hminor0, hminor1]
  simp
  field_simp [hy]
  ring
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution {K : Type*} [Field K]
    (r : Rank) (y : K) (hy : 1 + y ≠ 0) :
    Matrix.det (cyclicBMatrix r y) = y / (1 + y) := by
  cases r with
  | three => exact det_bThree y hy
  | four => exact det_bFour y hy
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
