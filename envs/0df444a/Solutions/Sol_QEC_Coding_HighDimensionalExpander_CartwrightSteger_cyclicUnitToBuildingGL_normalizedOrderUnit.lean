-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicUnitToBuildingGL_normalizedOrderUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:46:55.52964+00:00
-- url     : https://prove2.me/submissions/0dc911bf-5200-4300-bb0b-9edd8f3d951e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicUnitToBuildingGL_orderYUnit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) (q : ℤ) :
    cyclicUnitToBuildingGL P r
        (orderUnitToCyclicUnit P r (normalizedOrderUnit P r u q)) =
      (Matrix.GeneralLinearGroup.scalar (Fin r.matrixRank)
          (buildingLocalYUnit P)) ^ (-q) *
        cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u) := by
  rw [normalizedOrderUnit, map_mul, map_zpow,
    map_mul, map_zpow, cyclicUnitToBuildingGL_orderYUnit]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
