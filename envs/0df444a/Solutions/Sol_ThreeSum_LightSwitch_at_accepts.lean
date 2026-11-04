-- Prove2me | solution 1 for ThreeSum.LightSwitch.at_accepts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:56.641103+00:00
-- url     : https://prove2.me/submissions/28aa08bc-5344-4398-826f-d201edfe83fa

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Theorems.Thm_ThreeSum_LightSwitch_accepts_iff
import Theorems.Thm_ThreeSum_PrimeDensity_mem_candidates
import Theorems.Thm_ThreeSum_Switch_accepts_iff
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_switchIndex_mem
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightSwitch
theorem _root_.solution {J j r : ℕ} (hne : (Switch.candidates J j r).Nonempty) :
    left J j r ≤ factor J j*cubic r (Switch.switchIndex J j r) :=
  (accepts_iff _ _ _ _).mp (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).2
end ThreeSum.LightSwitch
