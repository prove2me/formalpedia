-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusGL_mul_constantRegularMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:52:00.377608+00:00
-- url     : https://prove2.me/submissions/128f09bc-a4d5-440d-8869-25c14a2007c0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusGL_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r) :
    (frobeniusGL P r :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) *
        constantRegularMatrix P r c =
      constantRegularMatrix P r (constantFrobenius P r c) *
        (frobeniusGL P r :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank) (BaseField P)) := by
  rw [frobeniusGL_coe, constantRegularMatrix,
    Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
    ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  ext x
  simp [Module.End.mul_apply]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
