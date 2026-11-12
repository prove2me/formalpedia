-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticCoordinate_to_functionField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:26:22.841945+00:00
-- url     : https://prove2.me/submissions/caa2e3d5-15fe-4f9e-9b32-848faf39bb6e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_arithmetic_coordinate_of_cartwrightStegerOrder


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    arithmeticRingToFunctionField P
        (cartwrightStegerOrderArithmeticCoordinate P r x p) =
      (functionFieldCyclicBasis P r).repr
        (cartwrightStegerOrderToCyclicAlgebra P r x) p :=
  Classical.choose_spec
    (exists_arithmetic_coordinate_of_cartwrightStegerOrder P r x p)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
