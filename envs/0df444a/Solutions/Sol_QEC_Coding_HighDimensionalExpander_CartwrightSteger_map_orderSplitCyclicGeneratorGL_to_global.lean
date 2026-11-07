-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitCyclicGeneratorGL_to_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:02:31.020017+00:00
-- url     : https://prove2.me/submissions/9f9154da-85f3-4d60-a393-2ba17ad5bb59

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitCyclicGeneratorMatrix_to_global

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    orderSplitBaseChangeGLHom P r
        (orderSplitCyclicGeneratorGL P r) =
      cyclicGenerator P r := by
  apply Units.ext
  exact map_orderSplitCyclicGeneratorMatrix_to_global P r
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
