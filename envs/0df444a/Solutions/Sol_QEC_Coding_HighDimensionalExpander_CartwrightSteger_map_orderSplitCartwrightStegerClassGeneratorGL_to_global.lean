-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderSplitCartwrightStegerClassGeneratorGL_to_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:52:33.658881+00:00
-- url     : https://prove2.me/submissions/c756e90f-46c8-448d-a686-1700f19747eb

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitConstantGL_to_global
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderSplitBGL_to_global

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    orderSplitBaseChangeGLHom P r
        (orderSplitCartwrightStegerGeneratorGL P r
          (constantClassRepresentative P r u)) =
      cartwrightStegerGenerator P r u := by
  rw [orderSplitCartwrightStegerGeneratorGL, cartwrightStegerGenerator,
    map_mul, map_mul, map_inv, map_orderSplitConstantGL_to_global,
    map_orderSplitBGL_to_global]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
