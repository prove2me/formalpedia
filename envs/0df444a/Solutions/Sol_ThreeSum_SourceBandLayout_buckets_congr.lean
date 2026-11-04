-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.buckets_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:32.356261+00:00
-- url     : https://prove2.me/submissions/01933cf9-1fa2-49f1-8daf-e35aac36618a

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_SourceBandLayout_offset_congr
import Theorems.Thm_ThreeSum_SourceBandLayout_position_congr

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {μ : ℕ → ℤ} {key key' : ℕ → ℕ} {N M offsets flat : ℕ}
    (H : Stored μ key N M offsets flat) (he : ∀ i < N, key i=key' i) :
    Stored μ key' N M offsets flat := by
  refine ⟨?_,?_⟩
  · intro r hr
    rw [← offset_congr he]
    exact H.offsets r hr
  · intro i hi
    rw [← position_congr he hi]
    exact H.indices i hi
end ThreeSum.SourceBandLayout
