-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_integralArithmetic_coordinate_of_order_and_buildingIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:05:23.662942+00:00
-- url     : https://prove2.me/submissions/ecdf5455-3720-4500-883e-de3b85f8e3e9

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingCyclicCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_ArithmeticCyclicCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_arithmetic_coordinate_of_cartwrightStegerOrder
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_arithmetic_building_integer_intersection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_buildingInteger_coordinate_of_cyclicAlgebra_integral


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CartwrightStegerOrder P r)
    (hlocal : ∃ M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (BuildingIntegerRing P),
      M.map (SphericalHecke.integerEmbedding (BaseField P)) =
        cyclicAlgebraToBuilding P r
          (cartwrightStegerOrderToCyclicAlgebra P r x))
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    ∃ a : IntegralArithmeticRing P,
      integralArithmeticToFunctionField P a =
        (functionFieldCyclicBasis P r).repr
          (cartwrightStegerOrderToCyclicAlgebra P r x) p := by
  let z := (functionFieldCyclicBasis P r).repr
    (cartwrightStegerOrderToCyclicAlgebra P r x) p
  have harithmetic : ∃ a : ArithmeticRing P,
      arithmeticRingToFunctionField P a = z :=
    exists_arithmetic_coordinate_of_cartwrightStegerOrder P r x p
  have hbuilding : ∃ f : BuildingIntegerRing P,
      SphericalHecke.integerEmbedding (BaseField P) f =
        functionFieldToBuildingLocalField P z :=
    exists_buildingInteger_coordinate_of_cyclicAlgebra_integral
      P r (cartwrightStegerOrderToCyclicAlgebra P r x) hlocal p
  exact arithmetic_building_integer_intersection P z harithmetic hbuilding
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
