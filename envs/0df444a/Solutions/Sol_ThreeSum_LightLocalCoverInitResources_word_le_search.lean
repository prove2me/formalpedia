-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.word_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:33.913503+00:00
-- url     : https://prove2.me/submissions/621facc8-7a54-4108-9446-bc3d9b4a8054

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_word_bound
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_envelope_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_word_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_word_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverInit.word (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n :=
  (word_bound _).trans (envelope_le_search hh)
end ThreeSum.LightLocalCoverInitResources
