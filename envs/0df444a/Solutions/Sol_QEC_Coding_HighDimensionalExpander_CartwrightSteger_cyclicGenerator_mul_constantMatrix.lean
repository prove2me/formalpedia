-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGenerator_mul_constantMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:13.930491+00:00
-- url     : https://prove2.me/submissions/55cbd03e-9495-4005-8dc1-4952504009b5

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_symm_pow_pred

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank)
    (c : ConstantExtension P r) :
    cyclicGeneratorMatrix P r * constantMatrix P r c =
      constantMatrix P r (constantFrobenius P r c) *
        cyclicGeneratorMatrix P r := by
  have hwrap := congrArg (fun e :
      ConstantExtension P r ≃ₐ[BaseField P] ConstantExtension P r => e c)
    (constantFrobenius_symm_pow_pred P r)
  cases r with
  | three =>
      ext i j
      simp only [constantMatrix]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;>
        simp [cyclicGeneratorMatrix] at hwrap ⊢
      rw [hwrap]
      exact mul_comm _ _
  | four =>
      ext i j
      simp only [constantMatrix]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;>
        simp [cyclicGeneratorMatrix] at hwrap ⊢
      rw [hwrap]
      exact mul_comm _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
