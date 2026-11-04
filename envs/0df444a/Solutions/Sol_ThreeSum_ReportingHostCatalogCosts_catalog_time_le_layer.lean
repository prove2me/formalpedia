-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogCosts.catalog_time_le_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:05:25.63326+00:00
-- url     : https://prove2.me/submissions/fe40959c-a052-41fb-b00d-b13926e1e4c9

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
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
import Definitions.Def_WeightedCache3SUM_Alias_aee3f2a8e7e7d37a
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
import Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_downsetCap_add_one_le_layer


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogCosts
set_option maxRecDepth 8000
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts
namespace ThreeSum.ReportingHostCatalogCosts
theorem _root_.solution {W V offset cut n : ℕ} (hfit : offset+V ≤ W)
    (hhalf : cut ≤ V/2) (hn : 0 < n) :
    LightReportingSuffixCatalogSetup.time W V cut offset n ≤
      100000*(W+1)^5*n*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have ht := LightReportingSuffixCatalogSetup.time_bound (n := n) hfit hcut
  have hc := downsetCap_add_one_le_layer hhalf
  have hv : V+2 ≤ 2*(W+1) := by omega
  have hn' : n+1 ≤ 2*n := by omega
  calc
    _ ≤ 23000*(W+1)^4*((V+2)*V.choose cut)*(n+1) :=
      ht.trans (Nat.mul_le_mul_right (n+1) (Nat.mul_le_mul_left (23000*(W+1)^4) hc))
    _ ≤ 23000*(W+1)^4*((2*(W+1))*V.choose cut)*(2*n) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (23000*(W+1)^4) (Nat.mul_le_mul_right _ hv)) hn'
    _ = 92000*(W+1)^5*n*V.choose cut := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))
end ThreeSum.ReportingHostCatalogCosts
