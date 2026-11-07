-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGenerator_mul_constantMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:44:13.705815+00:00
-- url     : https://prove2.me/submissions/1af2c0a2-6046-4f71-95e1-1315343663d6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantFrobenius_symm_pow_pred
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ConstantExtension P r) :
    indexCyclicGeneratorMatrix P r level *
        indexConstantMatrix P r level c =
      indexConstantMatrix P r level (constantFrobenius P r c) *
        indexCyclicGeneratorMatrix P r level := by
  have hwrap := congrArg
    (fun e : ConstantExtension P r ≃ₐ[BaseField P]
        ConstantExtension P r => indexConstantEmbedding P r level (e c))
    (constantFrobenius_symm_pow_pred P r)
  cases r with
  | three =>
      ext i j
      simp only [indexConstantMatrix]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;>
        simp [indexCyclicGeneratorMatrix] at hwrap ⊢
      rw [hwrap]
      exact mul_comm _ _
  | four =>
      ext i j
      simp only [indexConstantMatrix]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;>
        simp [indexCyclicGeneratorMatrix] at hwrap ⊢
      rw [hwrap]
      exact mul_comm _ _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
