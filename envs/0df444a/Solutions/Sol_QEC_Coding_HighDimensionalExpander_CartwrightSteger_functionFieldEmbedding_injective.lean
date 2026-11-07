-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.functionFieldEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:00.296484+00:00
-- url     : https://prove2.me/submissions/287f2dea-da31-4360-b70c-6d90bb9feed0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    Function.Injective (functionFieldEmbedding P r) := by
  exact RingHom.injective _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
