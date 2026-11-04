-- Prove2me | solution 1 for ThreeSum.SourceBandPairSlices.histogram_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:18:52.781331+00:00
-- url     : https://prove2.me/submissions/3375bcca-9f9f-4af1-8475-939f7e7e5efd

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Theorems.Thm_ThreeSum_SourceBandLayout_flat_end_le_work


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
theorem _root_.solution {base n g m zero i bound : ℕ}
    (hb : work base n g m ≤ bound) (hz : zero+m ≤ bound) :
    histogramPtr base n g m zero i+m ≤ bound := by
  unfold histogramPtr
  split_ifs with hi
  · have hh := flat_end_le_work (base := base) (m := m) hi
    unfold flat cursor offsets codes at hh
    omega
  · exact hz
end ThreeSum.SourceBandPairSlices
