-- Prove2me | solution 1 for ThreeSum.LightBandRawAColor.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:51:37.493451+00:00
-- url     : https://prove2.me/submissions/15925edb-d531-4770-abe0-4d1867615aa2

import Definitions.Def_Submission_ThreeSum_LightColorBands
import Definitions.Def_Submission_ThreeSum_LightBandRawACatalog
import Definitions.Def_Submission_ThreeSum_BandRawAOriginal
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Theorems.Thm_ThreeSum_LightBandCandidates_time_bound
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_2186ec26acc49293
import Theorems.Thm_ThreeSum_LightBandRawACatalog_time_bound
import Theorems.Thm_ThreeSum_LightBandRawA_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightColorArray_time_bound
import Theorems.Thm_ThreeSum_LightColorBands_time_bound
import Theorems.Thm_ThreeSum_LightColorClasses_time_bound
import Theorems.Thm_ThreeSum_LightColorIndex_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAColor
open Light BandPartition BandCandidateRows BandRawA ColorClassLists
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBandRawAColor
theorem _root_.solution (W n g : ℕ) :
    time W n g ≤ 1200*(W+1)*(n+1)+ColorBandBounds.time n g+catalogTime n g+600 := by
  have h := LightColorBands.time_bound W n g
  unfold time
  omega
end ThreeSum.LightBandRawAColor
