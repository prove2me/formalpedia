-- Prove2me | solution 1 for ThreeSum.SourceBucketView.nodup_indices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:08.049755+00:00
-- url     : https://prove2.me/submissions/c50b20f5-de73-460c-a105-c9b2c16ae547

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_ThreeSum_SourceBucketView_indices_eq
import Theorems.Thm_ThreeSum_SourceBuckets_Stored_nodup_bucketList


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
namespace ThreeSum.SourceBucketView
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    (indices μ offsets flat r).Nodup := by
  rw [indices_eq H hr]
  exact H.nodup_bucketList hkey hr
end ThreeSum.SourceBucketView
