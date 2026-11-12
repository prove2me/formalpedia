-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_skewLaurent_of_order_and_buildingIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:25:27.673203+00:00
-- url     : https://prove2.me/submissions/352cfb08-748d-44c0-9a03-ae66761db256

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_of_integralCyclicCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_integralArithmetic_coordinate_of_order_and_buildingIntegral


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r x)) :
    ∃ f : CartwrightStegerSkewLaurentRing P r,
      skewLaurentToGlobalMatrix P r f =
        (cartwrightStegerOrderToCyclicAlgebra P r x).1 := by
  have hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr
            (cartwrightStegerOrderToCyclicAlgebra P r x) p := by
    intro p
    exact exists_integralArithmetic_coordinate_of_order_and_buildingIntegral
      P r x hlocal p
  exact exists_skewLaurent_of_integralCyclicCoordinates P r
    (cartwrightStegerOrderToCyclicAlgebra P r x) hcoords
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
