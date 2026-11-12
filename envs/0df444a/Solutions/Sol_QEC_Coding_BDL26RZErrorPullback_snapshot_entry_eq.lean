-- Prove2me | solution 1 for QEC.Coding.BDL26RZErrorPullback.snapshot_entry_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:05:50.765451+00:00
-- url     : https://prove2.me/submissions/80975f05-b19c-4b15-8e13-6ea6f4512e27

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_snapshot_output_eq
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_entryAt_step


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZErrorPullback
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge BDL26RZCohomology BDL26AlternatingCochain
open MultiscaleDecoder BDL26OwnerIncidenceMasks
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
variable (n : Nat) (sigma : BDL26CanonicalHistoryMarks.Input S n) (k : StepIndex n)
namespace QEC.Coding.BDL26RZErrorPullback
theorem _root_.solution (h : ¬ (LevelTwoHistory.physicalStep k).val % 2 = 0) :
    BDL26CanonicalHistoryMarks.entryAt S n sigma k.succ =
      CorrectionHistoryEntry.step k
        (LevelTwoHistory.suffixOutput (indexedDecoderData S (n + 2)) k
          (BDL26RZDecoderAdapter.rzStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
            (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ))) := by
  rw [BDL26CanonicalHistoryMarks.entryAt_step, snapshot_output_eq S n sigma k h]
end QEC.Coding.BDL26RZErrorPullback
