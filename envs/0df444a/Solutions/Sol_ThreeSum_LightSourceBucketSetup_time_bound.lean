-- Prove2me | solution 1 for ThreeSum.LightSourceBucketSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:49:17.946414+00:00
-- url     : https://prove2.me/submissions/44e2551a-45f8-4ffc-a5bb-ae016e06d2c8

import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_LightSourceBucketSetup
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketSetup
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketSetup
theorem _root_.solution (N M : ℕ) : time N M ≤ 500*(N+M+1) := by
  have hb := LightSourceBucketBuild.time_bound N M
  unfold time
  omega
end ThreeSum.LightSourceBucketSetup
