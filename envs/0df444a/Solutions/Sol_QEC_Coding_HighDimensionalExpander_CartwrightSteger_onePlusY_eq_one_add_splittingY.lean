-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusY_eq_one_add_splittingY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:52:05.674776+00:00
-- url     : https://prove2.me/submissions/18358523-3cbd-44fb-b6d9-bcf16d97629d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    onePlusY P r = 1 + splittingY P r := by
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
