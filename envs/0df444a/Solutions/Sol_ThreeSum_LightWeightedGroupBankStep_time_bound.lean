-- Prove2me | solution 1 for ThreeSum.LightWeightedGroupBankStep.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:27.001208+00:00
-- url     : https://prove2.me/submissions/e228abcd-4257-48da-9afe-11903ce2b8a8

import Definitions.Def_Submission_Weighted_GroupedBanks
import Definitions.Def_Submission_Weighted_GroupBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightWeightedBankSweep_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupBankStep
namespace ThreeSum.LightWeightedGroupBankStep
theorem _root_.solution (N L n : ℕ) : time N L n≤30000*(N+1)*(N+L+1)*(n+1) := by
  have hb := LightWeightedBankAssembly.time_bound N L n
  have hpos : 1≤(N+1)*(N+L+1) := Nat.succ_le_of_lt (by positivity)
  have hs := Nat.mul_le_mul_right (n+1) hpos
  unfold time Light.copyTime
  nlinarith only [hb,hs]
end ThreeSum.LightWeightedGroupBankStep
