-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixQueryIndexed.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:38:43.488144+00:00
-- url     : https://prove2.me/submissions/8fe2f343-6049-4c25-b339-ff31b2ed7af5

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryHost
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
import Theorems.Thm_ThreeSum_BlockIndexedQuery_suffixStage_le
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
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_residual_le_suffix
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixExplicit_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixLower_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixQueryHost_time_bound
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


set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixQueryIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.LightReportingSuffixQueryIndexed
theorem _root_.solution {h J k t : ℕ} (ht : t ≤ residualSize h J k+1) :
    LightReportingSuffixQueryHost.time (width h J) (suffixStage J (512*h) k) (residualSize h J k) t ≤
      18000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
  LightReportingSuffixQueryHost.time_bound (suffixStage_le J (512*h) k)
    LightReportingSuffixBoxes.residual_le_suffix ht
end ThreeSum.LightReportingSuffixQueryIndexed
