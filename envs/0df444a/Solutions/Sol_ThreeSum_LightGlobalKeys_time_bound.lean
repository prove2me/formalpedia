-- Prove2me | solution 1 for ThreeSum.LightGlobalKeys.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:18.605191+00:00
-- url     : https://prove2.me/submissions/b04505b5-058a-4dc7-9c43-5a067745f199

import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightGlobalKeys
import Theorems.Thm_ThreeSum_LightGlobalKeys_localCount_pos
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_a98211a6e8223f5f
import Theorems.Thm_ThreeSum_LightRadixRows_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalKeys
open Light GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open LightSubsetAddress SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightGlobalKeys
theorem _root_.solution (h J : ℕ) :
    time h J ≤ 2000*(512*h+1)*(outputCount (512*h) h+1)*(scheduleSize h+1)+
      300*(J+1)*(localCount h^J+1)+200 := by
  have he := LightSubsetEnumerationSetup.time_bound (512*h) (2*h)
  have hl := LightLocalKeys.time_bound (512*h) (outputCount (512*h) h) (scheduleSize h)
  have hg := LightRadixKeys.time_bound (localCount h) J (localCount_pos h)
  have hc : 800*(512*h+1)*(outputCount (512*h) h+1) ≤
      800*(512*h+1)*(outputCount (512*h) h+1)*(scheduleSize h+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  change LightSubsetEnumerationSetup.time (512*h) (2*h) ≤
    800*(512*h+1)*(outputCount (512*h) h+1) at he
  unfold time
  nlinarith
end ThreeSum.LightGlobalKeys
