-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantFrobenius_symm_pow_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:51:49.816376+00:00
-- url     : https://prove2.me/submissions/4e0427b2-bb5f-418c-bf72-6cf0702223f6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_pow_matrixRank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    (constantFrobenius P r).symm ^ (r.matrixRank - 1) =
      constantFrobenius P r := by
  change (constantFrobenius P r)⁻¹ ^ (r.matrixRank - 1) =
    constantFrobenius P r
  calc
    (constantFrobenius P r)⁻¹ ^ (r.matrixRank - 1) =
        (constantFrobenius P r ^ r.matrixRank)⁻¹ *
          constantFrobenius P r := by
      cases r <;> simp [Rank.matrixRank] <;> group
    _ = constantFrobenius P r := by
      rw [constantFrobenius_pow_matrixRank]
      simp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
