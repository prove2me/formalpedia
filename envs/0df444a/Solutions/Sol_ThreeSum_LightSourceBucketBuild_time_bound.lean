-- Prove2me | solution 1 for ThreeSum.LightSourceBucketBuild.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:43:20.47717+00:00
-- url     : https://prove2.me/submissions/5a6da376-8b9d-4bc7-a1e9-3cbaffa8ee85

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketBuild

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketBuild
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketBuild
theorem _root_.solution (N M : ℕ) : time N M ≤ 300*(N+M+1) := by
  unfold time histogramTime countTime fillTime LightSourceBucketFromHistogram.time
    LightSourceBucketOffsets.time LightSourceBucketScatter.time
  omega
end ThreeSum.LightSourceBucketBuild
