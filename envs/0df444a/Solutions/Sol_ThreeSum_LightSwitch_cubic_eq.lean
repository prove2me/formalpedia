-- Prove2me | solution 1 for ThreeSum.LightSwitch.cubic_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:54.266738+00:00
-- url     : https://prove2.me/submissions/5f59441c-993a-45a8-b352-9ce81d30e778

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightSwitch
theorem _root_.solution (r q : ℕ) : cubic r q=Switch.cubicNumerator r q := by
  unfold cubic Switch.cubicNumerator
  ring
end ThreeSum.LightSwitch
