-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.actual_coboundary1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:29:38.468992+00:00
-- url     : https://prove2.me/submissions/1a028653-2809-4638-907a-dde2add0a843

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
theorem _root_.solution (j : LevelIndex depth) :
    (indexedDecoderData S depth).family.coboundary1 j =
      (indexedFamily S depth).coboundary1 j := rfl
end QEC.Coding.BDL26RXXStarTransport
