-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupedSources.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:21.034663+00:00
-- url     : https://prove2.me/submissions/1e53f8b3-170c-4aa1-9f48-992411046b2d

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSources
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_time_bound
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedSources
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryGroupedSources
theorem _root_.solution (L count bank groups : ℕ) :
    time L count bank groups≤1000*(L+1)*(count+groups*bank+1) := by
  have hk := LightTernaryGroupedSourceKeys.time_bound L count
  have hh := LightTernaryWeightedHistogram.time_bound count (groups*bank)
  unfold time LightTernarySourceHistogram.scaleTime
  nlinarith [Nat.zero_le (L*(groups*bank))]
end ThreeSum.LightTernaryGroupedSources
