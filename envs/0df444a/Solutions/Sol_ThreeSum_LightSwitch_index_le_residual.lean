-- Prove2me | solution 1 for ThreeSum.LightSwitch.index_le_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:47.368247+00:00
-- url     : https://prove2.me/submissions/bb082c94-374d-4a0c-88ee-e5c1f08abcc0

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Theorems.Thm_ThreeSum_PrimeDensity_mem_candidates
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_switchIndex_mem
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightSwitch
theorem _root_.solution {J j r : ℕ} (hne : (Switch.candidates J j r).Nonempty) :
    Switch.switchIndex J j r ≤ r :=
  (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).1.trans (Nat.div_le_self _ _)
end ThreeSum.LightSwitch
