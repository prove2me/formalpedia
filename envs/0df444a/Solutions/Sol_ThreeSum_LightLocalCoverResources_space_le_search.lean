-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.space_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:25.301907+00:00
-- url     : https://prove2.me/submissions/7a88b07b-b177-4577-969a-c8a9184a677a

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_space_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search
import Definitions.Def_WeightedCache3SUM_Alias_f0a4e431f2aa2c77


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution {n base : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    space base (Scales.microHalf (Scales.inputBits n)) ≤ base+Scales.localSearch 4000000 n :=
  (space_bound _ _).trans (Nat.add_le_add_left (envelope_le_search hh) base)
end ThreeSum.LightLocalCoverResources
