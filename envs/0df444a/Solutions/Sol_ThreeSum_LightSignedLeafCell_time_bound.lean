-- Prove2me | solution 1 for ThreeSum.LightSignedLeafCell.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:43.334491+00:00
-- url     : https://prove2.me/submissions/0b9caefe-5328-4ee4-b264-80108c32ecff

import Definitions.Def_Submission_ThreeSum_LightSignedLeafGeneral
import Definitions.Def_Submission_ThreeSum_LightSignedLeafCell
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafCell
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedLeafCell
theorem _root_.solution (W : ℕ) : time W ≤ 9300*(W+1)^2 := by
  have hl := LightSignedLeafGeneral.time_bound W
  have ha := LightDownsetAddress.time_bound W
  have hp : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  unfold time
  omega
end ThreeSum.LightSignedLeafCell
