-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicGeneratorMatrix_mem_cyclicAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:43.978586+00:00
-- url     : https://prove2.me/submissions/15a4e892-0d7c-43d6-89fa-7009dc015df4

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    cyclicGeneratorMatrix P r ∈ CyclicAlgebra P r := by
  apply Algebra.subset_adjoin
  exact Set.mem_union_right _ (Set.mem_insert _ _)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
