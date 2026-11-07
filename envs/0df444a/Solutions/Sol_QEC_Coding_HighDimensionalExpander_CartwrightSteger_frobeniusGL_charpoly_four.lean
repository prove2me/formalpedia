-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_charpoly_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:02.383211+00:00
-- url     : https://prove2.me/submissions/41266fba-1694-491a-b93d-510d7ab6defe

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_toMatrix_normalBasis_four
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
private theorem normalCycle_four_charpoly (K : Type*) [Field K] :
    (!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] :
      Matrix (Fin 4) (Fin 4) K).charpoly =
      Polynomial.X ^ 4 - (1 : Polynomial K) := by
  rw [Matrix.charpoly]
  have hmatrix :
      (!![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] :
        Matrix (Fin 4) (Fin 4) K).charmatrix =
      !![Polynomial.X, 0, 0, -1; -1, Polynomial.X, 0, 0;
        0, -1, Polynomial.X, 0; 0, 0, -1, Polynomial.X] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.charmatrix]
  rw [hmatrix]
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, Fin.sum_univ_four]
  have h31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [h31, h32]
  simp
  ring
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
set_option maxHeartbeats 800000
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) :
    (frobeniusGL P .four : Matrix (Fin Rank.four.matrixRank)
      (Fin Rank.four.matrixRank) (BaseField P)).charpoly =
      Polynomial.X ^ Rank.four.matrixRank -
        (1 : Polynomial (BaseField P)) := by
  rw [frobeniusGL_coe]
  calc
    _ = LinearMap.charpoly
        (constantFrobenius P .four).toLinearEquiv.toLinearMap :=
      (LinearMap.charpoly_toMatrix
        (constantFrobenius P .four).toLinearEquiv.toLinearMap
        (constantBasis P .four))
    _ = (LinearMap.toMatrix (frobeniusNormalBasis P .four)
          (frobeniusNormalBasis P .four)
          (constantFrobenius P .four).toLinearEquiv.toLinearMap).charpoly :=
      (LinearMap.charpoly_toMatrix _ _).symm
    _ = _ := by rw [constantFrobenius_toMatrix_normalBasis_four]
                exact normalCycle_four_charpoly (BaseField P)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
