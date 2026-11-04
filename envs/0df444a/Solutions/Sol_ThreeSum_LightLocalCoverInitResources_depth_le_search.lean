-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.depth_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:02:18.879252+00:00
-- url     : https://prove2.me/submissions/1f7b6ddc-1928-4537-a44c-e6ab74b3ba5e

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_depth_bound
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_envelope_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_depth_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    512*Scales.microHalf (Scales.inputBits n)+9 ≤ Scales.localSearch 5000000 n :=
  (depth_bound _).trans (envelope_le_search hh)
end ThreeSum.LightLocalCoverInitResources
