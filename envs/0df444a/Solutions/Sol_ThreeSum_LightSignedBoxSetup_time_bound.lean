-- Prove2me | solution 1 for ThreeSum.LightSignedBoxSetup.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:54.398824+00:00
-- url     : https://prove2.me/submissions/e2c0acdf-ae62-4fd5-858f-8e3ea96f7f93

import Definitions.Def_Submission_ThreeSum_LightSignedLeafTable
import Definitions.Def_Submission_ThreeSum_LightSignedBoxSetup
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafCell_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafTable_time_bound
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
open ThreeSum ThreeSum.LightSignedBoxSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedBoxSetup
theorem _root_.solution {W cut : ℕ} (hcut : cut ≤ W) :
    time W cut ≤ 19000*(W+1)^4*(downsetCap W cut+1) := by
  have hl := LightSignedLeafTable.time_bound hcut
  have hb := LightBoxStages.time_bound hcut
  have hp : (W+1)^3 ≤ (W+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm := Nat.mul_le_mul_right (downsetCap W cut+1) (Nat.mul_le_mul_left 12000 hp)
  have hpos : 1 ≤ (W+1)^4*(downsetCap W cut+1) := by
    have hh : 0 < (W+1)^4*(downsetCap W cut+1) := by positivity
    omega
  unfold time
  nlinarith
end ThreeSum.LightSignedBoxSetup
