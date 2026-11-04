-- Prove2me | solution 1 for ThreeSum.LightWeightedBankSweep.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:03:40.468114+00:00
-- url     : https://prove2.me/submissions/b4e219cf-9075-4530-9e28-a88417d5dbb0

import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_BankResources
import Theorems.Thm_ThreeSum_LightWeightedBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankSweep
namespace ThreeSum.LightWeightedBankSweep
theorem _root_.solution (N L n : ℕ) : time N L n≤4000*(N+1)*(N+L+1)*(n+1) := by
  have hc := LightWeightedBankCoordinate.time_bound N L n
  have hm := Nat.mul_le_mul_left N hc
  unfold time
  nlinarith only [hm]
end ThreeSum.LightWeightedBankSweep
