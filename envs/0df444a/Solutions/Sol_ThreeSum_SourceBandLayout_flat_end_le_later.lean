-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.flat_end_le_later
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:38.948747+00:00
-- url     : https://prove2.me/submissions/ebd3451a-0b30-4aaf-912f-bfa5c23cf73a

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_SourceBandLayout_hist_mono
import Theorems.Thm_ThreeSum_SourceBandLayout_flat_end

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {base n g m i k : ℕ} (hik : i < k) :
    flat base n g m i+cap n g ≤ hist base n g m k := by
  rw [flat_end]
  exact hist_mono base n g m (by omega)
end ThreeSum.SourceBandLayout
