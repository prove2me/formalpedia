-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.depth_four_indices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:33:45.88222+00:00
-- url     : https://prove2.me/submissions/afd0339e-4f9e-43dc-b6da-993bbcb3c39f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalXStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26LevelTwoDistance
open BDL26ReplacementCochainMaps BDL26RZDecoderAdapter BDL26RZErrorPullback
open BDL26RZFiniteBlockTransport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
namespace QEC.Coding.BDL26RZPhysicalXStarTransport
theorem _root_.solution : (topStep 0).val=3 ∧ (rxStep 0).val=2 ∧
    (topStep 0).succ.val=4 ∧ (rxStep 0).castSucc.val=2 := by decide
end QEC.Coding.BDL26RZPhysicalXStarTransport
