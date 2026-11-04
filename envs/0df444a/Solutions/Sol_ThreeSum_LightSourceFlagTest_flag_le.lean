-- Prove2me | solution 1 for ThreeSum.LightSourceFlagTest.flag_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:04.431983+00:00
-- url     : https://prove2.me/submissions/a3890279-2e8f-48fa-8b66-7dcfb2db0b64

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceFlagTest
open Light
namespace ThreeSum.LightSourceFlagTest
theorem _root_.solution (card required count cap : ℕ) : flag card required count cap ≤ 1 := by
  unfold flag
  split <;> omega
end ThreeSum.LightSourceFlagTest
