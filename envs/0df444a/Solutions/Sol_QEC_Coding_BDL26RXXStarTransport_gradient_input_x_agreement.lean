-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.gradient_input_x_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:55:46.515693+00:00
-- url     : https://prove2.me/submissions/10ea5bcf-c20f-4265-b99a-6bb90f3535cc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_actual_coboundary1
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_boundaryGradient_kernel
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_eq_of_word_add_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_error_other_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradientError_restriction
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradientError_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXXStarTransport
theorem _root_.solution (x y : XCoord S i) (a : Upper S depth i) :
    restrictWordLinear ((rxLx S depth i h).syndromeRegion y) (errorSyndrome S depth i a).val =
      restrictWordLinear ((rxLx S depth i h).syndromeRegion y)
        (errorSyndrome S depth i (a+gradientError S depth i h x)).val := by
  have hz : restrictWordLinear ((rxLx S depth i h).syndromeRegion y)
      ((indexedFamily S depth).coboundary1 i.succ (gradientError S depth i h x))=0 := by
    rw [← actual_coboundary1 S depth,
      (rxContract S depth i h).support_decomposition.cxDelta1_restriction_global]
    by_cases hy : y=x
    · subst y
      rw [gradientError_restriction,boundaryGradient_kernel]
    · rw [error_other_x_zero S depth i h x y hy _ (gradientError_supported S depth i h x),map_zero]
  apply eq_of_word_add_zero
  change restrictWordLinear _ ((indexedFamily S depth).coboundary1 i.succ a) +
    restrictWordLinear _ ((indexedFamily S depth).coboundary1 i.succ
      (a+gradientError S depth i h x))=0
  rw [← map_add,← map_add,← add_assoc,word_add_self,zero_add]
  exact hz
end QEC.Coding.BDL26RXXStarTransport
