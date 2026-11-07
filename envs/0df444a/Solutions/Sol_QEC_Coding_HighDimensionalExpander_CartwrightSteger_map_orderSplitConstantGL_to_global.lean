-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitConstantGL_to_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:51:27.357505+00:00
-- url     : https://prove2.me/submissions/5b5aec79-8f33-473b-a151-5cc6a94c5099

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitConstantMatrix_to_global

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u : (ConstantExtension P r)ˣ) :
    orderSplitBaseChangeGLHom P r
        (orderSplitConstantGLHom P r u) =
      constantUnitMatrix P r u := by
  apply Units.ext
  exact map_orderSplitConstantMatrix_to_global P r u
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
