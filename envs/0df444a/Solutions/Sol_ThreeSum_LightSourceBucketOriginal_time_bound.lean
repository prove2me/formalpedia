-- Prove2me | solution 1 for ThreeSum.LightSourceBucketOriginal.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:43:23.042132+00:00
-- url     : https://prove2.me/submissions/8c943e45-e98f-4c51-a453-fce34e0adf47

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketOriginal
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketOriginal
theorem _root_.solution (N p m U D : ℕ) :
    time N p m U D ≤ 498*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+233*m+333 := by
  have hh := LightSourceHistogram.time_bound N p m U D
  have hb := LightSourceBucketFromHistogram.time_bound N m
  unfold time
  nlinarith
end ThreeSum.LightSourceBucketOriginal
