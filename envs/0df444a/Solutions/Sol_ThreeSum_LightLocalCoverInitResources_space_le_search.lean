-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.space_le_search
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:51.280824+00:00
-- url     : https://prove2.me/submissions/c79c026c-bd54-4289-b699-99471b52e671

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_space_bound
import Theorems.Thm_ThreeSum_LightLocalCoverInitResources_envelope_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_envelope_le_search
import Theorems.Thm_ThreeSum_LightLocalCoverResources_space_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search
import Definitions.Def_WeightedCache3SUM_Alias_f0a4e431f2aa2c77


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution {n free : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverInit.space free (Scales.microHalf (Scales.inputBits n)) ≤
      free+Scales.localSearch 5000000 n :=
  (space_bound _ _).trans (Nat.add_le_add_left (envelope_le_search hh) free)
end ThreeSum.LightLocalCoverInitResources
