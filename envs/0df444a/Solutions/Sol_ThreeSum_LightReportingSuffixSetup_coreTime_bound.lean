-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixSetup.coreTime_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:29.879634+00:00
-- url     : https://prove2.me/submissions/91f08e2d-b144-41d8-937f-231382d0cf05

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightExplicitSum_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
import Theorems.Thm_ThreeSum_LightMaskMinimum_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightQueryBox_time_bound
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixBatch_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_306830be6786141e
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafCell_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafTable_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightSparseQuery_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}
namespace ThreeSum.LightReportingSuffixSetup
theorem _root_.solution {W V cut : ℕ} (hV : V ≤ W) (hcut : cut ≤ V) :
    coreTime W V cut ≤ 19000*(W+1)^4*(downsetCap V cut+1) := by
  have hl := LightReportingSuffixTable.time_bound hV hcut
  have hb := LightBoxStages.time_bound hcut
  have hp : (W+1)^3 ≤ (W+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hv := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 4
  have hm := Nat.mul_le_mul_right (downsetCap V cut+1) (Nat.mul_le_mul_left 12000 hp)
  have hn := Nat.mul_le_mul_right (downsetCap V cut+1) (Nat.mul_le_mul_left 6000 hv)
  have hpos : 1 ≤ (W+1)^4*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold coreTime
  nlinarith
end ThreeSum.LightReportingSuffixSetup
