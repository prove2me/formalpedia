-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.remainder_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:29:41.827858+00:00
-- url     : https://prove2.me/submissions/a97240b7-b14a-44a6-9c1a-dbf642e6ccdf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_potential_boundary_cocycle
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_updated_delta


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
theorem _root_.solution (x : XCoord S i) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (remainder S depth i h x a b) =
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by
  rw [remainder,map_add,potential_boundary_cocycle,add_zero,updated_delta]
end QEC.Coding.BDL26RXXStarTransport
