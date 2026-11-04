-- Prove2me | solution 1 for ThreeSum.LightReportingPrefixArrays.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:44:58.980962+00:00
-- url     : https://prove2.me/submissions/214a79ec-fc99-4c11-84a6-4f6c667968a7

import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
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
open ThreeSum ThreeSum.LightReportingPrefixArrays
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration ReportingHostPairSegments
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : Limits}
namespace ThreeSum.LightReportingPrefixArrays
theorem _root_.solution {L h k : ℕ} (hh : 2*h ≤ L) :
    time L h k ≤ 5000*(L+1)^2*(localCount L h+1)+
      600*(k+1)*((localCount L h)^k+1)+300 := by
  have hp := LightReportingPairRows.time_bound hh
  have hk := LightRadixKeys.time_bound (localCount L h) k
    (Nat.one_le_of_lt (Nat.mul_pos (Nat.choose_pos hh) (Nat.choose_pos (by omega))))
  unfold time powTableTime
  change LightReportingPairRows.time L h ≤ 4000*(L+1)^2*(localCount L h+1) at hp
  nlinarith
end ThreeSum.LightReportingPrefixArrays
