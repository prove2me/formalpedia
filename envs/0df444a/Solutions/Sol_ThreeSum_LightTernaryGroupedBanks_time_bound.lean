-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupedBanks.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:29.860651+00:00
-- url     : https://prove2.me/submissions/1bebece9-a8c3-416a-957d-c22fc320e8e9

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedBanks
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankResources
import Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankSweep_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedBanks
namespace ThreeSum.LightTernaryGroupedBanks
theorem _root_.solution (groups N L n : ℕ) :
    time groups N L n≤31000*(groups+1)*(N+1)*(N+L+1)*(n+1) := by
  have hb := LightTernaryGroupBankStep.time_bound N L n
  have hm := Nat.mul_le_mul_left groups hb
  have hpos : 1≤(N+1)*(N+L+1)*(n+1) := Nat.succ_le_of_lt (by positivity)
  have hs := Nat.mul_le_mul_left groups hpos
  unfold time
  nlinarith only [hm,hs,hpos]
end ThreeSum.LightTernaryGroupedBanks
