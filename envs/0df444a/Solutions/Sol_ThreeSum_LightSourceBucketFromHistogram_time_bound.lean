-- Prove2me | solution 1 for ThreeSum.LightSourceBucketFromHistogram.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:37:11.295685+00:00
-- url     : https://prove2.me/submissions/172d4d22-2065-4808-ac73-fcf2742897f8

import Definitions.Def_Submission_ThreeSum_LightSourceBucketOffsets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketScatter
import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketFromHistogram
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketFromHistogram
theorem _root_.solution (N M : ℕ) : time N M ≤ 220*(N+M+1) := by
  unfold time LightSourceBucketOffsets.time LightSourceBucketScatter.time
  omega
end ThreeSum.LightSourceBucketFromHistogram
