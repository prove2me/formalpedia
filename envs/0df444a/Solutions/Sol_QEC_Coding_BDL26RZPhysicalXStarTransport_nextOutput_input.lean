-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.nextOutput_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:32:15.670409+00:00
-- url     : https://prove2.me/submissions/625e5646-bb9d-4c3c-bbd7-d096d3d0568b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_topOutput_eq


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
theorem _root_.solution (S : OddScale) (j : Nat) (a : Upper S (2*j+4) (topStep j)) :
    (nextOutput S j a).input=(topOutput S j a).coarse := by
  rw [topOutput_eq]
  exact (BDL26OwnerIncidenceMasks.actualStep_relation S (2*j+4) (rxStep j)).input_eq _
end QEC.Coding.BDL26RZPhysicalXStarTransport
