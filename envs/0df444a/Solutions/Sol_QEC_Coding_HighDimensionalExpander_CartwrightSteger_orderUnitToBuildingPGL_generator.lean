-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToBuildingPGL_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:33:55.866202+00:00
-- url     : https://prove2.me/submissions/7a2b4ee9-8c46-43e1-a0f7-5f40ab53ad5d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToCyclicUnit_generator
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGeneratorCyclicUnit_to_buildingPGL
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGeneratorCyclicUnit_to_buildingPGL



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToBuildingPGL P r (cartwrightStegerOrderUnitGenerator P r x) =
      buildingCartwrightStegerGenerator P r x := by
  rw [orderUnitToBuildingPGL, MonoidHom.comp_apply,
    orderUnitToCyclicUnit_generator,
    cartwrightStegerGeneratorCyclicUnit_to_buildingPGL]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
