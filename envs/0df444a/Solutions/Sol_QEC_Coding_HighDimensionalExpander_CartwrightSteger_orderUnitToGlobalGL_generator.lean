-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToGlobalGL_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:33:52.317116+00:00
-- url     : https://prove2.me/submissions/d2333fc2-5ded-4998-9283-8e25274dbbcd

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitToCyclicUnit_generator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToGlobalGL P r (cartwrightStegerOrderUnitGenerator P r x) =
      cartwrightStegerGenerator P r x := by
  rw [orderUnitToGlobalGL, MonoidHom.comp_apply,
    orderUnitToCyclicUnit_generator]
  apply Units.ext
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
