-- Prove2me | solution 1 for ThreeSum.LightTernaryInversePass.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:33.502128+00:00
-- url     : https://prove2.me/submissions/36af7809-a3f8-4ee3-8540-cd689bace170

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryInversePass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryInversePass
theorem _root_.solution (L n : ℕ) : time L n ≤ 800*(L+1)*(n+1) := by
  have h := LightTernaryLookup.time_bound L
  unfold time
  nlinarith
end ThreeSum.LightTernaryInversePass
