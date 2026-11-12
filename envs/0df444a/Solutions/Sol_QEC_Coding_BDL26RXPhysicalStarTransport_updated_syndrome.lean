-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalStarTransport.updated_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:24:51.493206+00:00
-- url     : https://prove2.me/submissions/f97fa0af-37d2-407a-b102-8165573fbfa9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_updated_delta


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
theorem _root_.solution (a b : Upper S depth i) :
    (indexedFamily S depth).coboundary1 i.succ (updated S depth i h a b)=
      ((indexedDecoderData S depth).selectedMap i).map2 (coarseSum S depth i h a b).val :=
  BDL26RXErrorPullback.updated_delta S depth i h a b
end QEC.Coding.BDL26RXPhysicalStarTransport
