-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceLayout.join_space_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:01:00.625198+00:00
-- url     : https://prove2.me/submissions/36d0be57-fdfd-434e-9bce-256cbb46e8b8

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_Ready_next
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_Stored_next


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaSourceLayout
open WeightedGlobalArenaLayout TernarySourceExecutionFactory LightTernarySourceHost
namespace ThreeSum.WeightedGlobalArenaSourceLayout
theorem _root_.solution (free M NL NR U : ℕ) (input dictionary : ℕ→ℤ) :
    LightWantedSetup.space free M input dictionary NL NR U 0 0=
      free+LightWantedSetup.space 0 M input dictionary NL NR U 0 0 := by
  have hp : LightWantedSetup.pairBase free NL NR M=
      free+LightWantedSetup.pairBase 0 NL NR M := by
    unfold LightWantedSetup.pairBase LightWantedSetup.bucketBase LightWantedSetup.rightCodes
      LightWantedSetup.leftCodes LightSourceBucketSetup.next
    omega
  unfold LightWantedSetup.space LightSourceResidues.space
  rw [hp]
  omega
end ThreeSum.WeightedGlobalArenaSourceLayout
