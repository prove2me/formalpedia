-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.map1_eq_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:23:16.4602+00:00
-- url     : https://prove2.me/submissions/cf4d3ba0-c2a0-46c7-ae94-4f69dc11bb3f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_localized_blocks
import Theorems.Thm_QEC_Coding_BDL26RXFiniteBlockTransport_map1_eq_remainder
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map1_eq_remainder


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
    ((indexedDecoderData S depth).selectedMap i).map1 (L S depth i h u a b)=R S depth i h u a b :=
  BDL26RXFiniteBlockTransport.map1_eq_remainder S depth i h _ _ a b
    (localized_blocks S depth i h u a b he)
end QEC.Coding.BDL26RXPhysicalStarTransport
