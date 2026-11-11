-- Prove2me | solution 1 for QEC.Coding.BDL26RZErrorPullback.snapshot_output_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:07:05.594438+00:00
-- url     : https://prove2.me/submissions/b3575d20-70eb-467d-83fc-d53add0b5bb9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Indexed
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback

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
    BDL26CanonicalHistoryMarks.outputAt S n sigma k =
      BDL26RZDecoderAdapter.rzStepOutput S (n + 2) (LevelTwoHistory.physicalStep k) h
        (BDL26CanonicalHistoryMarks.inputAt S n sigma k.succ) := by
  unfold BDL26CanonicalHistoryMarks.outputAt
  rw [actualStep_rz S (n + 2) (LevelTwoHistory.physicalStep k) h]
end QEC.Coding.BDL26RZErrorPullback
