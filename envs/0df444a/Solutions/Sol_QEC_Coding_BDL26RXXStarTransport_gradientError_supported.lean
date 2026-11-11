-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.gradientError_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:04:56.301273+00:00
-- url     : https://prove2.me/submissions/68e537ed-7344-4c01-9f51-4cfaf3bb87ad

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_support_of_zero_off

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
    hammingSupport (gradientError S depth i h x) ⊆ (rxLx S depth i h).correctionRegion x := by
  apply support_of_zero_off
  intro p hp
  exact dif_neg hp
end QEC.Coding.BDL26RXXStarTransport
