-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixBatch.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:19.2249+00:00
-- url     : https://prove2.me/submissions/3772c828-0d8b-4b0d-8cee-b37456fcfe8c

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBatch
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
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
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
open ThreeSum ThreeSum.LightReportingSuffixBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
open ReportingHostSuffix
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixBatch
theorem _root_.solution {W V : ℕ} (hV : V ≤ W) (n : ℕ) :
    time W V n ≤ 9400*(W+1)^2*(n+1) := by
  have h := LightReportingSuffixCell.time_bound hV
  have hmul := Nat.mul_le_mul_left n h
  have hpoly : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  have hsmall := Nat.mul_le_mul_left n (show 65 ≤ 100*(W+1)^2 by omega)
  unfold time
  nlinarith
end ThreeSum.LightReportingSuffixBatch
