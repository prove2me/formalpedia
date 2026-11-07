-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.projective_generator_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:13.028209+00:00
-- url     : https://prove2.me/submissions/34211310-50f7-4346-b275-19bf7259d4ca

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_mem_group

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    cartwrightStegerToProjective P r (cartwrightStegerGenerator P r u) ∈
      CartwrightStegerProjectiveGroup P r := by
  exact ⟨cartwrightStegerGenerator P r u,
    cartwrightStegerGenerator_mem_group P r u, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
