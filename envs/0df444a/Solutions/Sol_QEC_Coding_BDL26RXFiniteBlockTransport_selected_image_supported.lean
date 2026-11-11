-- Prove2me | solution 1 for QEC.Coding.BDL26RXFiniteBlockTransport.selected_image_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:02:25.794201+00:00
-- url     : https://prove2.me/submissions/80500c28-6bc3-4f45-9bd9-97ee4020fb6a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_coarse_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_support_eq
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_support_eq
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_support_eq


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
theorem _root_.solution (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) (he : Localized S depth i h X0 Q0 a b) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) ⊆
      (neighborZ S depth i X0 Q0).biUnion (zPairImage (rxData S depth i h)) := by
  rw [selected_image_support_eq]
  intro p hp
  obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨z,coarse_supported S depth i h X0 Q0 a b he hz,hp⟩
end QEC.Coding.BDL26RXFiniteBlockTransport
