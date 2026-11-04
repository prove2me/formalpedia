-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:56.581989+00:00
-- url     : https://prove2.me/submissions/426a81fe-3ba0-4e21-b99b-22ccef281275

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_parameters_envelope_le
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_constant_le
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_four_envelope_le
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_metadata_time_le
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightLocalCounts_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverRow_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightPairFlags_time_bound
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_ea9db4f154655ba6
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightDecode_time_bound
import Theorems.Thm_ThreeSum_LightWeightGather_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_e3ac3137889c3add


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution (h : ℕ) : LightLocalCoverInit.time h ≤ envelope h := by
  have hp := (LocalParameterBounds.time_bound h).trans (parameters_envelope_le h)
  have hc := LightLocalCoverResources.time_bound h
  have hm := metadata_time_le h
  have hk := constant_le h
  apply (show LightLocalCoverInit.time h ≤ 4*LightLocalCoverResources.envelope h from ?_).trans
    (four_envelope_le h)
  unfold LightLocalCoverInit.time
  omega
end ThreeSum.LightLocalCoverInitResources
