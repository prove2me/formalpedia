-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitToCyclicUnit_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:29:19.891984+00:00
-- url     : https://prove2.me/submissions/4d9702f3-b2be-4df5-9c14-7c1b6b2753cc

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    orderUnitToCyclicUnit P r (cartwrightStegerOrderUnitGenerator P r x) =
      cartwrightStegerGeneratorCyclicUnit P r x := by
  apply Units.ext
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
