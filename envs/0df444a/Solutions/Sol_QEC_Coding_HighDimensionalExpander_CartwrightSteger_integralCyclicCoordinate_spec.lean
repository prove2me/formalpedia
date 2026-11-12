-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralCyclicCoordinate_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:13:28.520325+00:00
-- url     : https://prove2.me/submissions/fe6212c0-8bb6-4d79-a482-717eac094f56

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    integralArithmeticToFunctionField P
        (integralCyclicCoordinate P r x hcoords p) =
      (functionFieldCyclicBasis P r).repr x p :=
  Classical.choose_spec (hcoords p)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
