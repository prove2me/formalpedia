-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.outputAt_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:51:09.228112+00:00
-- url     : https://prove2.me/submissions/26316d12-daff-4f78-9155-cb31c430527c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (i : StepIndex n) :
    (outputAt S n sigma i).input = inputAt S n sigma i.succ :=
  (actualStep_relation S (n + 2) (LevelTwoHistory.physicalStep i)).input_eq _
end QEC.Coding.BDL26CanonicalHistoryMarks
