-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.header_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:49.981065+00:00
-- url     : https://prove2.me/submissions/085c83be-4087-4f01-88d5-a7a84a2480ba

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_SourceBandLayout_data_le_hist

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {base n g m i : ℕ} (hi : i < size n g) :
    base+6*i+6 ≤ hist base n g m i := by
  have hb := data_le_hist base n g m i
  unfold data at hb
  omega
end ThreeSum.SourceBandLayout
