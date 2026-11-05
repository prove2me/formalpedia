-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceLayout.join_space_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:28:08.635251+00:00
-- url     : https://prove2.me/submissions/c284cac5-f45d-473f-9856-9ecca9959b0a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceLayout
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_Ready_next
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_Stored_next


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceLayout
open WeightedGlobalArenaLayout TernarySourceExecutionFactory LightTernarySourceHost
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceLayout
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceLayout
