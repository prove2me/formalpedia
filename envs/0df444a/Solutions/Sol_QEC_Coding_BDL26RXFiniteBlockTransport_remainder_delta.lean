-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.remainder_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:03:26.936486+00:00
-- url     : https://prove2.me/submissions/394ca1f9-f137-49de-8dac-a5a6cb209158

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_phi_boundary_cocycle
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_updated_delta


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXFiniteBlockTransport
theorem _root_.solution (X0 : Finset (XCoord S i)) (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (R S depth i h X0 a b) =
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val := by
  rw [R,map_add,phi_boundary_cocycle,add_zero,updated_delta]
end QEC.Coding.BDL26RXFiniteBlockTransport
