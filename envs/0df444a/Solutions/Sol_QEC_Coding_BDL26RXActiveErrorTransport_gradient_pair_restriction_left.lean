-- Prove2me | solution 1 for QEC.Coding.BDL26RXActiveErrorTransport.gradient_pair_restriction_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:48:33.259194+00:00
-- url     : https://prove2.me/submissions/ad8e8ff8-aad8-4da3-852e-de0f9b620386

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_error_other_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_error_other_x_zero
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradientError_restriction
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_gradientError_supported


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXActiveErrorTransport
theorem _root_.solution (x0 x1 : XCoord S i) (hn : x0≠x1) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x0)
      (gradientError S depth i h x0+gradientError S depth i h x1)=boundaryGradient S depth i h x0 := by
  rw [map_add,gradientError_restriction,
    BDL26RXXStarTransport.error_other_x_zero S depth i h x1 x0 hn _
      (gradientError_supported S depth i h x1),add_zero]
end QEC.Coding.BDL26RXActiveErrorTransport
