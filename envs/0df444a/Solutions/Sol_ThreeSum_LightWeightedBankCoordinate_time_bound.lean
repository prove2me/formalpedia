-- Prove2me | solution 1 for ThreeSum.LightWeightedBankCoordinate.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:59:22.663255+00:00
-- url     : https://prove2.me/submissions/5fa83c3b-68a8-44c5-8da7-af039a23eeb5

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankCoordinate
namespace ThreeSum.LightWeightedBankCoordinate
theorem _root_.solution (N L n : ℕ) : time N L n≤3000*(N+L+1)*(n+1) := by
  have hm := LightTernaryMetadata.time_bound (2*N) n
  have hp := LightTernaryPass.time_bound L n
  unfold time
  nlinarith only [hm,hp]
end ThreeSum.LightWeightedBankCoordinate
