-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.selected_image_exterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:24:39.008061+00:00
-- url     : https://prove2.me/submissions/7ac5e9d5-e5ce-4953-93a8-9fa3829b7e86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_selected_image_exterior
import Theorems.Thm_QEC_Coding_BDL26RXQBlockTransport_selected_image_exterior
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_selected_image_exterior


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
theorem _root_.solution (a b : Upper S depth i) (p : FamilyZ S depth i.succ)
    (hp : p ∉ (rxData S depth i h).zSector) :
    ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val p=0 :=
  BDL26RXFiniteBlockTransport.selected_image_exterior S depth i h a b p hp
end QEC.Coding.BDL26RXPhysicalStarTransport
