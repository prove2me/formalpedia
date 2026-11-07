-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.toLin_one_sub_frobeniusGL_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:52:43.0269+00:00
-- url     : https://prove2.me/submissions/7e5e44b3-aae2-4632-a3c1-b0fab77e6d0b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_coe


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    Matrix.toLin (constantBasis P r) (constantBasis P r)
        (1 - ((frobeniusGL P r)⁻¹ :
          Matrix.GeneralLinearGroup (Fin r.matrixRank) (BaseField P))) =
      frobeniusDifferenceLinearMap P r := by
  have hinv : Matrix.toLin (constantBasis P r) (constantBasis P r)
      ((frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))⁻¹) =
      (constantFrobenius P r).symm.toLinearEquiv.toLinearMap := by
    have hF : Matrix.toLin (constantBasis P r) (constantBasis P r)
        (frobeniusGL P r :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) =
        (constantFrobenius P r).toLinearEquiv.toLinearMap := by
      rw [frobeniusGL_coe, Matrix.toLin_toMatrix]
    ext x
    apply (constantFrobenius P r).injective
    rw [show constantFrobenius P r
        ((constantFrobenius P r).symm.toLinearEquiv.toLinearMap x) = x by
      exact (constantFrobenius P r).apply_symm_apply x]
    change (constantFrobenius P r).toLinearEquiv.toLinearMap
        (Matrix.toLin (constantBasis P r) (constantBasis P r)
          ((frobeniusGL P r :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))⁻¹) x) = x
    rw [← hF]
    rw [← Matrix.toLin_mul_apply]
    rw [show (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) *
          (frobeniusGL P r :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P))⁻¹ = 1 by
      rw [← Matrix.GeneralLinearGroup.coe_inv]
      exact congrArg Units.val (mul_inv_cancel (frobeniusGL P r))]
    rw [Matrix.toLin_one, LinearMap.id_apply]
  rw [map_sub, Matrix.toLin_one]
  rw [Matrix.GeneralLinearGroup.coe_inv, hinv]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
