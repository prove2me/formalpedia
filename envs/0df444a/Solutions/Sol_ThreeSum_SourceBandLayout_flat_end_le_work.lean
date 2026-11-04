-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.flat_end_le_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:49.330227+00:00
-- url     : https://prove2.me/submissions/d393675c-e458-4dd0-9b34-9ebae208c522

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
theorem _root_.solution {base n g m i : ℕ} (hi : i < size n g) :
    flat base n g m i+cap n g ≤ work base n g m := by
  rw [flat_end]
  exact hist_mono base n g m (by omega)
end ThreeSum.SourceBandLayout
