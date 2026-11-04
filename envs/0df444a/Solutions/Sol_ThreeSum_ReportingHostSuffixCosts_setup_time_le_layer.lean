-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffixCosts.setup_time_le_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:36:44.492131+00:00
-- url     : https://prove2.me/submissions/2580de20-958b-47bb-a8d0-077c9a0de0b0

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_downsetCap_add_one_le_layer
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
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffixCosts
theorem _root_.solution {W V offset cut : ℕ} (hfit : offset+V ≤ W)
    (hhalf : cut ≤ V/2) :
    LightReportingSuffixSetup.time W V cut offset ≤ 40000*(W+1)^5*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have ht := LightReportingSuffixSetup.time_bound hfit hcut
  have hd := downsetCap_add_one_le_layer hhalf
  have hm := Nat.mul_le_mul_left (20000*(W+1)^4) hd
  have hv : V+2 ≤ 2*(W+1) := by omega
  have hm₂ := Nat.mul_le_mul_left (20000*(W+1)^4)
    (Nat.mul_le_mul_right (V.choose cut) hv)
  calc
    _ ≤ 20000*(W+1)^4*((V+2)*V.choose cut) := ht.trans hm
    _ ≤ 20000*(W+1)^4*((2*(W+1))*V.choose cut) := hm₂
    _ = _ := by ring
end ThreeSum.ReportingHostSuffixCosts
