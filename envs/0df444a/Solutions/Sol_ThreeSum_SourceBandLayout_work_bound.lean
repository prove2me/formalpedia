-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.work_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:40.640246+00:00
-- url     : https://prove2.me/submissions/ca4cb980-35db-4362-a425-5cd0800a3f55

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_SourceBandLayout_capacity_product_le

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution (base n g m : ℕ) (hg : 0 < g) :
    work base n g m ≤ base+4*n+size n g*(3*m+7) := by
  have hc := capacity_product_le n g hg
  unfold work hist data stride
  nlinarith
end ThreeSum.SourceBandLayout
