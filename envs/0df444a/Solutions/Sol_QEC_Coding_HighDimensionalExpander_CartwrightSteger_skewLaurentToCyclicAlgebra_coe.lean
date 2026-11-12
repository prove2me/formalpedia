-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToCyclicAlgebra_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:26:14.147042+00:00
-- url     : https://prove2.me/submissions/9c1396e0-740d-452e-9d6e-23c48b40097f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_OrderUnitReconstruction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingSkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCompatibility

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (f : CartwrightStegerSkewLaurentRing P r) :
    (skewLaurentToCyclicAlgebra P r f).1 =
      skewLaurentToGlobalMatrix P r f := rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
