-- Prove2me | solution 1 for ThreeSum.LightSharedReportingCounts.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:29:46.969786+00:00
-- url     : https://prove2.me/submissions/00830199-19fd-4d1a-82bf-03f4217a40e4

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Definitions.Def_Submission_ThreeSum_LightSharedReportingCounts
import Theorems.Thm_ThreeSum_LightPascal_buildTime_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingCounts
open Light LightPascal LightSubsetAddress SubsetAddress SharedReportingBankLayout
set_option maxHeartbeats 1700000
set_option maxRecDepth 9000
namespace ThreeSum.LightSharedReportingCounts
theorem _root_.solution (h : ℕ) : time h ≤ 1500*(512*h+1)^2 := by
  have hb := buildTime_bound (512*h)
  unfold time
  nlinarith [Nat.one_le_pow' 2 (512*h)]
end ThreeSum.LightSharedReportingCounts
