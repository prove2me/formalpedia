-- Prove2me | solution 1 for ThreeSum.SourceBucketView.mem_indices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:14.383796+00:00
-- url     : https://prove2.me/submissions/2812cde1-68e3-4b52-9f00-42b4c8cf2e5d

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Theorems.Thm_ThreeSum_SourceBucketView_indices_eq
import Definitions.Def_WeightedCache3SUM_Alias_eaf7b30abbd797a4


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBucketView
open SourceBuckets LightHistogram
namespace ThreeSum.SourceBucketView
theorem _root_.solution {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ indices μ offsets flat r ↔ i < N ∧ key i = r := by
  rw [indices_eq H hr]
  exact H.mem_bucketList hkey hr
end ThreeSum.SourceBucketView
