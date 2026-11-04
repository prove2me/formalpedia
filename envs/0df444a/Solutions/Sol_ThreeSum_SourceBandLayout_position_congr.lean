-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.position_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:12.948596+00:00
-- url     : https://prove2.me/submissions/ddd154cd-148c-4be9-9898-d8070067abc1

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_SourceBandLayout_count_congr
import Theorems.Thm_ThreeSum_SourceBandLayout_offset_congr

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {key key' : ℕ → ℕ} {N i : ℕ}
    (he : ∀ j < N, key j=key' j) (hi : i < N) :
    position key N i=position key' N i := by
  unfold position
  rw [he i hi,offset_congr he,count_congr he hi.le]
end ThreeSum.SourceBandLayout
