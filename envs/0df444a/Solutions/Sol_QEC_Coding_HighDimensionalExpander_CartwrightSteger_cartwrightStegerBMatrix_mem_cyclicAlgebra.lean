-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerBMatrix_mem_cyclicAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:04.114893+00:00
-- url     : https://prove2.me/submissions/9b72c47d-ffb4-4760-bf05-d45030aa10c9

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mem_cyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    cartwrightStegerBMatrix P r ∈ CyclicAlgebra P r := by
  exact (CyclicAlgebra P r).sub_mem (CyclicAlgebra P r).one_mem
    (cyclicGeneratorInverseMatrix_mem_cyclicAlgebra P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
