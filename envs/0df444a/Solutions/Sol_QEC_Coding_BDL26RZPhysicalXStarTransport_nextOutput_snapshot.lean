-- Prove2me | solution 1 for QEC.Coding.BDL26RZPhysicalXStarTransport.nextOutput_snapshot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:23:09.86364+00:00
-- url     : https://prove2.me/submissions/4a79468b-d463-4de0-9eff-8653189edcb5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_original_input_step
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_topOutput_eq
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    nextOutput S j a=BDL26CanonicalHistoryMarks.outputAt S (2*j+2)
      (errorSyndrome S (2*j+4) (topStep j) a) (nextSnapshotIndex j) := by
  let s := errorSyndrome S (2*j+4) (topStep j) a
  let t : StepIndex (2*j+2) := Fin.last (2*j+1)
  have hc := original_input_step S (2*j+2) s t
  have ht : BDL26CanonicalHistoryMarks.outputAt S (2*j+2) s t=
      run S (2*j+4) (topStep j) (topStep_odd j) a := topOutput_eq S j a
  have hinput : BDL26CanonicalHistoryMarks.inputAt S (2*j+2) s
      (nextSnapshotIndex j).succ=
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse := by
    change BDL26CanonicalHistoryMarks.inputAt S (2*j+2) s t.castSucc=_
    exact hc.trans (congrArg (fun O : AssemblyStepOutput
      (indexedDecoderData S (2*j+4)) (topStep j) => O.coarse) ht)
  change BDL26OwnerIncidenceMasks.actualStep S (2*j+4) (rxStep j)
      (run S (2*j+4) (topStep j) (topStep_odd j) a).coarse=
    BDL26OwnerIncidenceMasks.actualStep S (2*j+4) (rxStep j)
      (BDL26CanonicalHistoryMarks.inputAt S (2*j+2) s (nextSnapshotIndex j).succ)
  exact congrArg (BDL26OwnerIncidenceMasks.actualStep S (2*j+4) (rxStep j)) hinput.symm
end QEC.Coding.BDL26RZPhysicalXStarTransport
