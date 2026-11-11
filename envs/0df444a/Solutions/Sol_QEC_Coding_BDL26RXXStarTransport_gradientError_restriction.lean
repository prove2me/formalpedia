-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.gradientError_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:40:06.225514+00:00
-- url     : https://prove2.me/submissions/ec0d2241-93f0-4114-b107-671cd4cb0dd7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_region_restrict_extend


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
theorem _root_.solution (x : XCoord S i) :
    restrictWordLinear ((rxLx S depth i h).correctionRegion x) (gradientError S depth i h x) =
      boundaryGradient S depth i h x := region_restrict_extend _ _
end QEC.Coding.BDL26RXXStarTransport
