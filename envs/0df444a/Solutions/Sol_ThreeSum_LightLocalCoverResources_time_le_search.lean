-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.time_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:16.107019+00:00
-- url     : https://prove2.me/submissions/94d07bb9-b3c9-4cc4-a12d-52ca0d4a4699

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightLocalCounts_time_bound
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
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search
import Definitions.Def_WeightedCache3SUM_Alias_e3ac3137889c3add


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverSetup.time (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 4000000 n :=
  (time_bound _).trans (envelope_le_search hh)
end ThreeSum.LightLocalCoverResources
