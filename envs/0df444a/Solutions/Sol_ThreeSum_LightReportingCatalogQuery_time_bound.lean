-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogQuery.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:31:20.130983+00:00
-- url     : https://prove2.me/submissions/d56a0a34-b0d1-4699-b07d-61ab39a9e02a

import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogSelection
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
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
import Definitions.Def_WeightedCache3SUM_Alias_a98211a6e8223f5f
import Theorems.Thm_ThreeSum_LightRadixRows_time_bound
import Theorems.Thm_ThreeSum_LightReportingPairRows_time_bound
import Theorems.Thm_ThreeSum_LightReportingPrefixArrays_time_bound
import Theorems.Thm_ThreeSum_LightReportingSortedCatalog_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixBatch_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_aee3f2a8e7e7d37a
import Theorems.Thm_ThreeSum_LightReportingSuffixCatalog_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixExplicit_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixQueryHost_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixQueryIndexed_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_d5b1b0bdde74f397
import Theorems.Thm_ThreeSum_LightReportingSuffixSetup_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixSum_time_bound
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
import Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_prefix_lookup_time_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingCatalogQuery
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostCatalogSelection
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.LightReportingCatalogQuery
theorem _root_.solution {h J k t : ℕ} (hk : k ≤ J) (ht : t ≤ residualSize h J k+1) :
    time h J k t ≤
      20000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) := by
  have hl := ReportingHostCatalogIndexCosts.prefix_lookup_time_le (h := h) hk
  have hq := LightReportingSuffixQueryIndexed.time_bound (h := h) (J := J) (k := k) ht
  have hbase : width h J+1 ≤ (width h J+1)^3 := Nat.le_self_pow (by omega) _
  have hm : (width h J+1)^3 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpos : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  change LightReportingCatalogLookup.time (width h J) (count h k) ≤ 1000*(width h J+1) at hl
  unfold time
  nlinarith
end ThreeSum.LightReportingCatalogQuery
