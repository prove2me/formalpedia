-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraSplitNormOne_eq_buildingNormOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:51:28.462271+00:00
-- url     : https://prove2.me/submissions/dacf40e2-e708-4ff8-8287-6d1e49623504

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_SplitCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraBuildingNormOne_eq_normOne

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    CyclicAlgebraSplitNormOne P r = CyclicAlgebraBuildingNormOne P r := by
  rw [cyclicAlgebraSplitNormOne_eq_normOne,
    cyclicAlgebraBuildingNormOne_eq_normOne]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
