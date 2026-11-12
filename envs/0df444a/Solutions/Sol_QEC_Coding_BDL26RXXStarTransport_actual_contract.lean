-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.actual_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:19:37.202705+00:00
-- url     : https://prove2.me/submissions/6c736afd-a494-432e-98ef-74948312b207

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry

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
theorem _root_.solution : (rxData S depth i h).contract = rxContract S depth i h := rfl
end QEC.Coding.BDL26RXXStarTransport
