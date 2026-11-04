-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupBankStep.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:40.432142+00:00
-- url     : https://prove2.me/submissions/26c93a08-46fa-4350-bcb3-43ec29a3a7ac

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedBanks
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankSweep_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupBankStep
namespace ThreeSum.LightTernaryGroupBankStep
theorem _root_.solution (N L n : ℕ) : time N L n≤30000*(N+1)*(N+L+1)*(n+1) := by
  have hb := LightTernaryBankAssembly.time_bound N L n
  have hpos : 1≤(N+1)*(N+L+1) := Nat.succ_le_of_lt (by positivity)
  have hs := Nat.mul_le_mul_right (n+1) hpos
  unfold time Light.copyTime
  nlinarith only [hb,hs]
end ThreeSum.LightTernaryGroupBankStep
