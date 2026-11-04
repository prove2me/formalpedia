-- Prove2me | solution 1 for ThreeSum.SourceBucketView.indices_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:50.448338+00:00
-- url     : https://prove2.me/submissions/7bdbaa7c-f7e3-4a59-aa7a-28cba5892838

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_ThreeSum_SourceBucketView_indices_eq
import Theorems.Thm_ThreeSum_SourceBuckets_bucketList_length


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
namespace ThreeSum.SourceBucketView
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    (indices μ offsets flat r).length = count key r N := by
  rw [indices_eq H hr,bucketList_length]
end ThreeSum.SourceBucketView
