-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.data_le_hist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:44:15.434773+00:00
-- url     : https://prove2.me/submissions/208ff8ed-724f-4e3c-ad0a-a3dc7d4e2df3

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution (base n g m i : ℕ) : data base n g ≤ hist base n g m i :=
  Nat.le_add_right _ _
end ThreeSum.SourceBandLayout
