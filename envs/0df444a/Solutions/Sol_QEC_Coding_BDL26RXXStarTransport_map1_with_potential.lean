-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.map1_with_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:02:03.980697+00:00
-- url     : https://prove2.me/submissions/92c2fcd0-79e1-4c7a-b071-04452306c78e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder

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
theorem _root_.solution (x : XCoord S i) (a b : Upper S depth i)
    (he : OneX S depth i h x a b) :
    ((indexedDecoderData S depth).selectedMap i).map1 (lowerWord S depth i h x a b) =
      updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ
        (potential S depth i h x a b) := map1_eq_remainder S depth i h x a b he
end QEC.Coding.BDL26RXXStarTransport
