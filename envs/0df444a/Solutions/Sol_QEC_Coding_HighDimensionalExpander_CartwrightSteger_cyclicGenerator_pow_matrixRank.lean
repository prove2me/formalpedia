-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_pow_matrixRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:52:12.519327+00:00
-- url     : https://prove2.me/submissions/87f7208c-ee24-470a-9ab9-274ef2c4943f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_shiftThree_pow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_shiftFour_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r ^ r.matrixRank =
      (onePlusY P r) • (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r)) := by
  cases r with
  | three => exact shiftThree_pow _ _
  | four => exact shiftFour_pow _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
