-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantMatrixEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:33.968363+00:00
-- url     : https://prove2.me/submissions/04c82e90-6a09-4d06-9d01-2b6408b470b3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_two_le_matrixRank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    Function.Injective (constantMatrixEmbedding P r) := by
  intro c d h
  let i0 : Fin r.matrixRank :=
    ⟨0, lt_of_lt_of_le (by omega) (Rank.two_le_matrixRank r)⟩
  have h00 := congrFun (congrFun h i0) i0
  simp [constantMatrix, i0] at h00
  exact RingHom.injective _ h00
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
