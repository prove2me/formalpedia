-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.nextOutput_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:40:21.564737+00:00
-- url     : https://prove2.me/submissions/6bb4d594-d733-449a-ac4c-6a5c1aad6f34

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_representatives_spec

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
theorem _root_.solution (S : OddScale) (j : Nat) (a b : Upper S (2*j+4) (topStep j)) :
    BDL26RXErrorPullback.run S (2*j+4) (rxStep j) (rxStep_even j) (firstRepresentative S j a)=nextOutput S j a ∧
    BDL26RXErrorPullback.run S (2*j+4) (rxStep j) (rxStep_even j) (secondRepresentative S j a b)=nextOutput S j b := by
  have hA : BDL26RXErrorPullback.errorSyndrome S (2*j+4) (rxStep j) (firstRepresentative S j a)=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse :=
    Subtype.ext (representatives_spec S j a b).1
  have hB : BDL26RXErrorPullback.errorSyndrome S (2*j+4) (rxStep j) (secondRepresentative S j a b)=
      (run S (2*j+4) (topStep j) (topStep_odd j) b).coarse :=
    Subtype.ext (representatives_spec S j a b).2.1
  constructor
  · rw [BDL26RXErrorPullback.run,hA,nextOutput,BDL26OwnerIncidenceMasks.actualStep_rx S (2*j+4) (rxStep j) (rxStep_even j)]
  · rw [BDL26RXErrorPullback.run,hB,nextOutput,BDL26OwnerIncidenceMasks.actualStep_rx S (2*j+4) (rxStep j) (rxStep_even j)]
end QEC.Coding.BDL26RZPhysicalXStarTransport
