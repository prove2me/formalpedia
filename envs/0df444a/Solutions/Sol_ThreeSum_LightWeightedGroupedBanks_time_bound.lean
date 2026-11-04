-- Prove2me | solution 1 for ThreeSum.LightWeightedGroupedBanks.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:39.31806+00:00
-- url     : https://prove2.me/submissions/d32fad27-22d8-4b44-a1fd-13fe0a139c44

import Definitions.Def_Submission_Weighted_GroupedBanks
import Definitions.Def_Submission_Weighted_GroupBankResources
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankSweep_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupedBanks
namespace ThreeSum.LightWeightedGroupedBanks
theorem _root_.solution (groups N L n : ℕ) :
    time groups N L n≤31000*(groups+1)*(N+1)*(N+L+1)*(n+1) := by
  have hb := LightWeightedGroupBankStep.time_bound N L n
  have hm := Nat.mul_le_mul_left groups hb
  have hpos : 1≤(N+1)*(N+L+1)*(n+1) := Nat.succ_le_of_lt (by positivity)
  have hs := Nat.mul_le_mul_left groups hpos
  unfold time
  nlinarith only [hm,hs,hpos]
end ThreeSum.LightWeightedGroupedBanks
