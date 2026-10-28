-- Prove2me | solution 1 for SensitivityCampaign.reach_213303
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:12:38.481819+00:00
-- url     : https://prove2.me/submissions/61eea9a9-8e01-4645-ae1f-2eca5a9c5c61

import Definitions.Def_BS2_b3ba934b_Endpoint40Seeds
import Theorems.Thm_SensitivityPublishing213303_periodic_upper
set_option autoImplicit false

theorem solution : SensitivityCampaign.AchievesExponent (213303/100000 : ℝ) := by
  exact ThreeBoundEndpoint40Seeds.achieves_213303_of_periodic_upper SensitivityPublishing213303.periodic_upper
