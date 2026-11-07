-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_charpoly_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:01.2042+00:00
-- url     : https://prove2.me/submissions/715fdcc6-c37a-4f72-90e2-1285823f50a5

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_toMatrix_normalBasis_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
private theorem normalCycle_three_charpoly (K : Type*) [Field K] :
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).charpoly =
      Polynomial.X ^ 3 - (1 : Polynomial K) := by
  rw [Matrix.charpoly]
  simp [Matrix.det_fin_three]
  ring
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
set_option maxHeartbeats 800000
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) :
    (frobeniusGL P .three : Matrix (Fin Rank.three.matrixRank)
      (Fin Rank.three.matrixRank) (BaseField P)).charpoly =
      Polynomial.X ^ Rank.three.matrixRank -
        (1 : Polynomial (BaseField P)) := by
  rw [frobeniusGL_coe]
  calc
    _ = LinearMap.charpoly
        (constantFrobenius P .three).toLinearEquiv.toLinearMap :=
      (LinearMap.charpoly_toMatrix
        (constantFrobenius P .three).toLinearEquiv.toLinearMap
        (constantBasis P .three))
    _ = (LinearMap.toMatrix (frobeniusNormalBasis P .three)
          (frobeniusNormalBasis P .three)
          (constantFrobenius P .three).toLinearEquiv.toLinearMap).charpoly :=
      (LinearMap.charpoly_toMatrix _ _).symm
    _ = _ := by rw [constantFrobenius_toMatrix_normalBasis_three]
                exact normalCycle_three_charpoly (BaseField P)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
