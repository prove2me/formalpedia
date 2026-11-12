-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.integralCyclicCoordinateSkew_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:11:20.624829+00:00
-- url     : https://prove2.me/submissions/05beca96-b47a-4cda-8319-2fd9397efa23

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_of_integralArithmetic


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
    skewLaurentToGlobalMatrix P r
        (integralCyclicCoordinateSkew P r x hcoords p) =
      functionFieldScalarMatrix P r
        (integralArithmeticToFunctionField P
          (integralCyclicCoordinate P r x hcoords p)) :=
  Classical.choose_spec (exists_skewLaurent_of_integralArithmetic P r
    (integralCyclicCoordinate P r x hcoords p))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
