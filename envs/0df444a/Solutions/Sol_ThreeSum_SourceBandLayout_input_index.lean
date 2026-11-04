-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.input_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:37.741117+00:00
-- url     : https://prove2.me/submissions/cffc63bd-88ab-4f9e-9391-999ac39cb62a

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {n g i j : ℕ} (hg : 0 < g) (hi : i < size n g) (hj : j < len n g i) :
    start g i+j < n := by
  have hlo := start_lt_stop hg hi
  have hhi := stop_le n g i
  unfold len at hj
  omega
end ThreeSum.SourceBandLayout
