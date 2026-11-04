-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.offset_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:57.969298+00:00
-- url     : https://prove2.me/submissions/616470be-70b0-4194-8420-1666160cc6d5

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_SourceBandLayout_count_congr

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {key key' : ℕ → ℕ} {N : ℕ}
    (he : ∀ i < N, key i=key' i) (r : ℕ) :
    SourceBuckets.offset key N r=SourceBuckets.offset key' N r := by
  unfold SourceBuckets.offset
  apply Finset.sum_congr rfl
  intro s _
  exact count_congr he le_rfl s
end ThreeSum.SourceBandLayout
