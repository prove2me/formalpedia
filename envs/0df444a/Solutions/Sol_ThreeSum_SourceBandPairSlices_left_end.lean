-- Prove2me | solution 1 for ThreeSum.SourceBandPairSlices.left_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:35.252383+00:00
-- url     : https://prove2.me/submissions/ca83e553-e650-4b4d-9c87-04e2fabe9c5d

import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Theorems.Thm_ThreeSum_SourceBandPairSlices_histogram_end
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_SourceBandPairData_ordered


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairSlices
open Light BandPartition SourceBandLayout SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
theorem _root_.solution (base NL NR g m i : ℕ) :
    histLeft base NL NR g m i+m ≤ next base NL NR g m := by
  have ho := ordered base NL NR g m
  exact histogram_end (by change rightBase base NL g m ≤ next base NL NR g m; omega)
    (by unfold next; omega)
end ThreeSum.SourceBandPairSlices
