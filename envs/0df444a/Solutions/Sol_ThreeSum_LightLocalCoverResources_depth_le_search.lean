-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.depth_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:34.752724+00:00
-- url     : https://prove2.me/submissions/b705e2e7-8ea4-4d31-bd67-8e33eb92b2db

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_depth_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    512*Scales.microHalf (Scales.inputBits n)+8 ≤ Scales.localSearch 4000000 n :=
  (depth_bound _).trans (envelope_le_search hh)
end ThreeSum.LightLocalCoverResources
