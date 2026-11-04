-- Prove2me | solution 1 for ThreeSum.LightSignedLeaf.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:05.762947+00:00
-- url     : https://prove2.me/submissions/f0218feb-5414-425f-b71d-795da0f0f11b

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightSign
import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeaf
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedLeaf
theorem _root_.solution (W : ℕ) : time W ≤ 5800*(W+1)^2 := by
  have ht := LightStageLookup.time_bound W
  unfold time LightSign.time
  nlinarith
end ThreeSum.LightSignedLeaf
