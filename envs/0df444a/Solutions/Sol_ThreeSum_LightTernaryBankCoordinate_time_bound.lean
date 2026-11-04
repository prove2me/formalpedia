-- Prove2me | solution 1 for ThreeSum.LightTernaryBankCoordinate.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:49.999875+00:00
-- url     : https://prove2.me/submissions/b49d41c1-d4e6-4b01-9483-d9e92394c170

import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankCoordinate
namespace ThreeSum.LightTernaryBankCoordinate
theorem _root_.solution (N L n : ℕ) : time N L n≤3000*(N+L+1)*(n+1) := by
  have hm := LightTernaryMetadata.time_bound (2*N) n
  have hp := LightTernaryPass.time_bound L n
  unfold time
  nlinarith only [hm,hp]
end ThreeSum.LightTernaryBankCoordinate
