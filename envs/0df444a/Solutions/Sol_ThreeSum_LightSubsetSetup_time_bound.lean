-- Prove2me | solution 1 for ThreeSum.LightSubsetSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:32:55.397341+00:00
-- url     : https://prove2.me/submissions/79c036b4-ae2b-413a-aec5-67e9692fb7da

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Theorems.Thm_ThreeSum_LightPascal_buildTime_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetSetup
theorem _root_.solution (L : ℕ) : time L ≤ 1200*(L+1)^2 := by
  have hb := buildTime_bound L
  unfold time powTableTime rankTime
  nlinarith
end ThreeSum.LightSubsetSetup
