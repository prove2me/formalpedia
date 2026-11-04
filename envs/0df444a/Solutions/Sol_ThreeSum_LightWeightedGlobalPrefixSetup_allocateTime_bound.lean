-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixSetup.allocateTime_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:58:04.882957+00:00
-- url     : https://prove2.me/submissions/93f64a1f-d23b-48d9-a34a-56a77701623a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_time_bound
import Theorems.Thm_ThreeSum_LightCacheEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearSource_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedGlobalPrefixSetup
theorem _root_.solution (m j : ℕ) :
    allocateTime m j≤ 1000*(N m j+1)*(nb m j+1)+20*j+1000 := by
  have hh:= time_bound m j
  unfold allocateTime LightNatPower.time
  nlinarith only [hh,Nat.zero_le (N m j*nb m j)]
end ThreeSum.LightWeightedGlobalPrefixSetup
