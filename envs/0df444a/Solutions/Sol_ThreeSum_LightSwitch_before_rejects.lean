-- Prove2me | solution 1 for ThreeSum.LightSwitch.before_rejects
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:55.473268+00:00
-- url     : https://prove2.me/submissions/c741ec28-b25e-4d7d-920e-c01228bb6e88

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Theorems.Thm_ThreeSum_LightSwitch_accepts_iff
import Theorems.Thm_ThreeSum_PrimeDensity_mem_candidates
import Theorems.Thm_ThreeSum_Switch_accepts_iff
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_switchIndex_le
import Theorems.Thm_ThreeSum_Switch_switchIndex_mem
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightSwitch
theorem _root_.solution {J j r q : ℕ}
    (hne : (Switch.candidates J j r).Nonempty) (hq : q < Switch.switchIndex J j r) :
    factor J j*cubic r q < left J j r := by
  have hb := (Switch.mem_candidates.mp (Switch.switchIndex_mem hne)).1
  have hno : ¬ Switch.accepts J j r q := by
    intro h
    have hm := Switch.switchIndex_le (Switch.mem_candidates.mpr ⟨by omega,h⟩)
    omega
  rw [accepts_iff] at hno
  omega
end ThreeSum.LightSwitch
