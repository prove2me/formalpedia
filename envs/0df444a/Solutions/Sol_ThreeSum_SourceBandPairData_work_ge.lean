-- Prove2me | solution 1 for ThreeSum.SourceBandPairData.work_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:31.06432+00:00
-- url     : https://prove2.me/submissions/9224a384-9f77-4668-98c8-086823900cbb

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_SourceBandPairData

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairData
open Light BandPartition
namespace ThreeSum.SourceBandPairData
theorem _root_.solution (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by
  unfold SourceBandLayout.work SourceBandLayout.hist SourceBandLayout.data
  omega
end ThreeSum.SourceBandPairData
