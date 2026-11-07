-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.shiftFour_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:50:05.504138+00:00
-- url     : https://prove2.me/submissions/694bd468-6eb3-417b-8a5d-129c907b3c82

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (K : Type*) [CommRing K] (a : K) :
    !![0, 0, 0, a; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] ^ 4 =
      a • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
