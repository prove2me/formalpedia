-- Prove2me | solution 1 for ThreeSum.LightSwitch.accepts_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:06:42.115444+00:00
-- url     : https://prove2.me/submissions/56401737-eaaa-4421-ab9c-7facbf8151f7

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Theorems.Thm_ThreeSum_LightSwitch_cubic_eq

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightSwitch
theorem _root_.solution (J j r q : ℕ) :
    Switch.accepts J j r q ↔ left J j r ≤ factor J j*cubic r q := by
  have hl : left J j r=(291*J+1000*j)*r^3 := by unfold left; ring
  rw [hl,cubic_eq]
  rfl
end ThreeSum.LightSwitch
