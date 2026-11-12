-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.selected_image_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:24:12.693011+00:00
-- url     : https://prove2.me/submissions/f76b549f-a89f-4c62-a5df-6c368c5c9d94

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_coarse_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_selected_image_support_eq
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_coarse_supported
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_support_eq
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_support_eq
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_coarse_supported
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_support_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
namespace QEC.Coding.BDL26RXPhysicalStarTransport
theorem _root_.solution (u : FamilyX S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    hammingSupport (((indexedDecoderData S depth).selectedMap i).map2
      (coarseSum S depth i h a b).val) ⊆
      (neighborZ S depth i h u).biUnion (zPairImage (rxData S depth i h)) := by
  rw [selected_image_support_eq]
  intro p hp
  obtain ⟨z,hz,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨z,coarse_supported S depth i h u a b he hz,hp⟩
end QEC.Coding.BDL26RXPhysicalStarTransport
