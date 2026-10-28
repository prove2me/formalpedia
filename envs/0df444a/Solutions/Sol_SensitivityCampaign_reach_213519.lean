-- Prove2me | solution 1 for SensitivityCampaign.reach_213519
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T21:10:33.022537+00:00
-- url     : https://prove2.me/submissions/b6b8a874-78a8-492e-a064-6c106da7dfc2

import Definitions.Def_BS2_b3ba934b_Endpoint16Seeds
import Theorems.Thm_SensitivityPublishing213519_periodic_upper
set_option autoImplicit false

theorem solution : SensitivityCampaign.AchievesExponent (213519/100000 : ℝ) := by
  exact ThreeBoundEndpoint16Seeds.achieves_213519_of_periodic_upper SensitivityPublishing213519.periodic_upper
