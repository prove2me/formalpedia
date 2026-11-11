-- Prove2me | solution 1 for QEC.Coding.BDL26RXXStarTransport.map2_x_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:41:17.862522+00:00
-- url     : https://prove2.me/submissions/53bc9517-7e56-4afd-8b29-842193b5c412

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXQBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_rx
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_map2_auxiliary_zero


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
theorem _root_.solution (tau : (indexedFamily S depth).Cochain2 i.castSucc)
    (x : XCoord S i) : restrictWordLinear ((rxLx S depth i h).syndromeRegion x)
      (((indexedDecoderData S depth).selectedMap i).map2 tau)=0 := by
  rw [selected_rx]
  funext p
  apply (rxData S depth i h).induced.map2_auxiliary_zero
  rw [← (rxData S depth i h).zSector_eq_induced]
  intro hz
  apply (Finset.disjoint_left.mp (rxData S depth i h).sectors_pairwise_disjoint.2.1) _ hz
  rw [(rxData S depth i h).xSector_eq_regions]
  exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,p.property⟩
end QEC.Coding.BDL26RXXStarTransport
