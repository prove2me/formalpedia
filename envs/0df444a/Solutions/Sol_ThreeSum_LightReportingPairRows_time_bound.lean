-- Prove2me | solution 1 for ThreeSum.LightReportingPairRows.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:40:19.541402+00:00
-- url     : https://prove2.me/submissions/418ca99e-14aa-4f51-ae5d-282193f17aa9

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingPairRows
import Theorems.Thm_ThreeSum_LayerCounts_vertex_degree_identity
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
open ThreeSum ThreeSum.LightReportingPairRows
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration
set_option maxHeartbeats 1800000
variable {lim : Limits}
namespace ThreeSum.LightReportingPairRows
theorem _root_.solution {L h : ℕ} (hh : 2*h ≤ L) :
    time L h ≤ 4000*(L+1)^2*(L.choose (2*h)*(2*h).choose h+1) := by
  have hdeg : 0 < (L-h).choose h := Nat.choose_pos (by omega)
  have hs := LightSubsetEnumerationSetup.time_bound L h
  have hq := LightQueryEnumeration.time_bound (t := h) (Nat.sub_le L h)
  have hlinear : L+1 ≤ (L+1)^2 := by nlinarith
  have hv : L.choose h ≤ L.choose h*(L-h).choose h := Nat.le_mul_of_pos_right _ hdeg
  have hm := Nat.mul_le_mul_left (L.choose h) hq
  rw [← LayerCounts.vertex_degree_identity]
  unfold time roundTime LightReportingAffine.time
  nlinarith
end ThreeSum.LightReportingPairRows
