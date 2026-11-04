-- Prove2me | solution 1 for ThreeSum.LightCanonicalBoxSum.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:40.746191+00:00
-- url     : https://prove2.me/submissions/f3573f48-16d2-4120-a0d3-978b7ef5f78c

import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightBoxSum
import Definitions.Def_Submission_ThreeSum_LightCanonicalBoxSum
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskMinimum_time_bound
import Theorems.Thm_ThreeSum_LightQueryBox_time_bound
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightCanonicalBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightCanonicalBoxSum
theorem _root_.solution {W c t : ℕ} (hc : c ≤ W) :
    time W c t ≤ 5200*(W+1)^2*(c.choose t+1) := by
  have he := LightQueryEnumeration.time_bound (t := t) hc
  have hs := LightBoxSum.time_bound W (c.choose t)
  have hp : 1 ≤ (W+1)^2*(c.choose t+1) := Nat.mul_pos (by positivity) (by omega)
  unfold time
  nlinarith
end ThreeSum.LightCanonicalBoxSum
