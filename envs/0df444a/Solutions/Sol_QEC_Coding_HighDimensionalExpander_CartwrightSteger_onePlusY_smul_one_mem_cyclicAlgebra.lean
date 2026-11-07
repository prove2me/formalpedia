-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.onePlusY_smul_one_mem_cyclicAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:15.944249+00:00
-- url     : https://prove2.me/submissions/4aef4102-dc85-44cd-b1c8-cb585da365fb

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_matrixRank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_mem_cyclicAlgebra

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    (onePlusY P r) •
        (1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) ∈
      CyclicAlgebra P r := by
  rw [← cyclicGenerator_pow_matrixRank]
  exact (CyclicAlgebra P r).pow_mem
    (cyclicGeneratorMatrix_mem_cyclicAlgebra P r) _
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
