-- Prove2me | solution 1 for ThreeSum.SourceBandPairSlices.right_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:23:34.644769+00:00
-- url     : https://prove2.me/submissions/e71d250f-ea0f-418b-aa68-de4282d52a6c

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Theorems.Thm_ThreeSum_SourceBandPairSlices_histogram_end
import Theorems.Thm_Light_Ends_next


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
theorem _root_.solution (base NL NR g m i : ℕ) :
    histRight base NL NR g m i+m ≤ next base NL NR g m := by
  exact histogram_end (by change zeroBase base NL NR g m ≤ next base NL NR g m; unfold next; omega)
    (by unfold next; omega)
end ThreeSum.SourceBandPairSlices
