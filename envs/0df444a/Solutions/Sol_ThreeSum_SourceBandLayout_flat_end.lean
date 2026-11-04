-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.flat_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:56.870967+00:00
-- url     : https://prove2.me/submissions/4cd82fb0-a531-4576-8d7c-5d772352efb4

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution (base n g m i : ℕ) :
    flat base n g m i+cap n g = hist base n g m (i+1) := by
  unfold flat cursor offsets codes hist stride
  ring
end ThreeSum.SourceBandLayout
