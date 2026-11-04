-- Prove2me | solution 1 for ThreeSum.LightTrimTest.flag_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:57.330642+00:00
-- url     : https://prove2.me/submissions/26480e23-90b3-4292-8572-5f407a7d670b

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTrimTest

set_option autoImplicit false
open ThreeSum ThreeSum.LightTrimTest
open Light
namespace ThreeSum.LightTrimTest
theorem _root_.solution (overlap leftCount rightCount cap : ℕ) : flag overlap leftCount rightCount cap ≤ 1 := by
  unfold flag
  split <;> omega
end ThreeSum.LightTrimTest
