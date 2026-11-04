-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixCatalogSetup.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:51:32.128994+00:00
-- url     : https://prove2.me/submissions/2b0a42e5-2579-4b31-b7ba-7b01f5cd3fd2

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
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
import Theorems.Thm_ThreeSum_LightReportingSuffixCatalog_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixSetup_time_bound
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
open ThreeSum ThreeSum.LightReportingSuffixCatalogSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix LightReportingSuffixCatalog
variable {lim : Limits}
namespace ThreeSum.LightReportingSuffixCatalogSetup
theorem _root_.solution {W V cut offset n : ℕ} (hfit : offset+V ≤ W) (hcut : cut ≤ V) :
    time W V cut offset n ≤ 23000*(W+1)^4*(downsetCap V cut+1)*(n+1) := by
  have hc := LightReportingSuffixCatalog.time_bound (n := n) hfit hcut
  have hs := LightDownsetSize.time_bound V
  have hV : V ≤ W := by omega
  have hp : (V+1)^2 ≤ (W+1)^4 :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hpos : 1 ≤ (W+1)^4*(downsetCap V cut+1)*(n+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm : (W+1)^4 ≤ (W+1)^4*(downsetCap V cut+1)*(n+1) :=
    (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
  unfold time
  nlinarith
end ThreeSum.LightReportingSuffixCatalogSetup
