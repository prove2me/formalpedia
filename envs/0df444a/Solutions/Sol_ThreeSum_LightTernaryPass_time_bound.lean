-- Prove2me | solution 1 for ThreeSum.LightTernaryPass.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:32.243477+00:00
-- url     : https://prove2.me/submissions/7c47748d-d93b-4484-a198-b70bf25ce68a

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryPass
theorem _root_.solution (L n : ℕ) : time L n ≤ 800*(L+1)*(n+1) := by
  have h := LightTernaryLookup.time_bound L
  unfold time
  nlinarith
end ThreeSum.LightTernaryPass
