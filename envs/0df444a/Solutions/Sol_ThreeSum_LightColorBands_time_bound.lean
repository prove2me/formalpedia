-- Prove2me | solution 1 for ThreeSum.LightColorBands.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:06.732556+00:00
-- url     : https://prove2.me/submissions/4c4874e9-1e97-4a73-b75e-498f4d592235

import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Definitions.Def_Submission_ThreeSum_ColorBandBounds
import Definitions.Def_Submission_ThreeSum_LightColorBands
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_2186ec26acc49293
import Theorems.Thm_ThreeSum_LightColorArray_time_bound
import Theorems.Thm_ThreeSum_LightColorClasses_time_bound
import Theorems.Thm_ThreeSum_LightColorIndex_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSortedBands_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightColorBands
open Light ColorClassLists
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightColorBands
theorem _root_.solution (W n g : ℕ) :
    time W n g ≤ 1200*(W+1)*(n+1)+ColorBandBounds.time n g+300 := by
  have h := LightColorClasses.time_bound W n
  unfold time
  omega
end ThreeSum.LightColorBands
