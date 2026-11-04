-- Prove2me | solution 1 for ThreeSum.LightTernaryBankSweep.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:18.782247+00:00
-- url     : https://prove2.me/submissions/ba8066ac-bca3-48b0-94cb-951fa8f17772

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankSweep
namespace ThreeSum.LightTernaryBankSweep
theorem _root_.solution (N L n : ℕ) : time N L n≤4000*(N+1)*(N+L+1)*(n+1) := by
  have hc := LightTernaryBankCoordinate.time_bound N L n
  have hm := Nat.mul_le_mul_left N hc
  unfold time
  nlinarith only [hm]
end ThreeSum.LightTernaryBankSweep
