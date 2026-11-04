-- Prove2me | solution 1 for ThreeSum.SourceFiniteInputs.selected_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:45.757579+00:00
-- url     : https://prove2.me/submissions/7b7a1fc7-b7f9-4466-92a6-3aec53889675

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Theorems.Thm_ThreeSum_GlobalKeyOffset_selected_lt
import Theorems.Thm_ThreeSum_LightGuardedWanted_selected_eq
import Theorems.Thm_ThreeSum_LightOriginalOffset_selected_lt
import Theorems.Thm_ThreeSum_RawAKeyLists_selected_lt


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule
namespace ThreeSum.SourceFiniteInputs
theorem _root_.solution (M P h J : ℕ) [NeZero M] (xs : List ℤ) :
    RawAKeyLists.selected M P xs h J < M := by
  rw [← LightGuardedWanted.selected_eq]
  exact LightOriginalOffset.selected_lt ..
end ThreeSum.SourceFiniteInputs
