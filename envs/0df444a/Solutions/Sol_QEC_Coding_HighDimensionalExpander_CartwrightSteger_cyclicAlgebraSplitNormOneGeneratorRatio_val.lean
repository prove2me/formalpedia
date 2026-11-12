-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOneGeneratorRatio_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:14:05.36699+00:00
-- url     : https://prove2.me/submissions/b14f373c-2bbd-4a65-b1fd-ab7a2f6873ba

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    (cyclicAlgebraSplitNormOneGeneratorRatio P r u v :
        (CyclicAlgebra P r)ˣ) =
      (cyclicAlgebraBuildingNormOneGeneratorRatio P r u v :
        (CyclicAlgebra P r)ˣ) :=
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
