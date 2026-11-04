-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.len_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:50:07.188172+00:00
-- url     : https://prove2.me/submissions/e120b884-ccdf-4dc2-a135-c3fcfb658ada

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_BandPartition_length_le


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution (n g i : ℕ) : len n g i ≤ cap n g := by
  have hn := stop_le n g i
  have hg := length_le n g i
  unfold len cap
  exact le_min (by omega) hg
end ThreeSum.SourceBandLayout
