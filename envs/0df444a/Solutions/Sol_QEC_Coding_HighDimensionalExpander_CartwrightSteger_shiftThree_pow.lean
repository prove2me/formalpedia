-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.shiftThree_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:50:04.630121+00:00
-- url     : https://prove2.me/submissions/2143e1d9-db34-4f21-90a1-cec664e7535a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (K : Type*) [CommRing K] (a : K) :
    !![0, 0, a; 1, 0, 0; 0, 1, 0] ^ 3 =
      a • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, pow_succ]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
