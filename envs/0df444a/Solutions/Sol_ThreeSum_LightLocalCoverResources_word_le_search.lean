-- Prove2me | solution 1 for ThreeSum.LightLocalCoverResources.word_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:06.971752+00:00
-- url     : https://prove2.me/submissions/6ad70066-3b89-44eb-b715-fedee7ff7836

import Definitions.Def_Submission_ThreeSum_LightLocalCoverSetup
import Definitions.Def_Submission_ThreeSum_LightLocalCoverCost
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_word_bound
import Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_word_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMagnitude
set_option maxHeartbeats 1800000
namespace ThreeSum.LightLocalCoverResources
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverSetup.word (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 4000000 n :=
  (word_bound _).trans (envelope_le_search hh)
end ThreeSum.LightLocalCoverResources
