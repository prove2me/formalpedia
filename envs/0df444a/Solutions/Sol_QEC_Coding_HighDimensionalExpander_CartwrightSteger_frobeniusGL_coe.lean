-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:49:43.280208+00:00
-- url     : https://prove2.me/submissions/7deefb38-4e9e-48a6-b368-cc43547d446f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) =
      LinearMap.toMatrix (constantBasis P r) (constantBasis P r)
        (constantFrobenius P r).toLinearEquiv.toLinearMap := by
  apply (Matrix.toLin (constantBasis P r) (constantBasis P r)).injective
  rw [Matrix.toLin_toMatrix]
  have hlin :
      Matrix.toLin (constantBasis P r) (constantBasis P r)
          (frobeniusGL P r :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) =
        ((Matrix.GeneralLinearGroup.toLin' (constantBasis P r))
          (frobeniusGL P r)).toLinearEquiv.toLinearMap := by
    ext x
    change
      Matrix.toLin (constantBasis P r) (constantBasis P r)
          (frobeniusGL P r :
            Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) x =
        ((Matrix.GeneralLinearGroup.toLin' (constantBasis P r))
          (frobeniusGL P r)).toLinearEquiv x
    rw [Matrix.GeneralLinearGroup.toLin'_apply, Matrix.toLin_apply]
    simp [Fintype.linearCombination_apply]
  rw [hlin, frobeniusGL, MulEquiv.apply_symm_apply]
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
