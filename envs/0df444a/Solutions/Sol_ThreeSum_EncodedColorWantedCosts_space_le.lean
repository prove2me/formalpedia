-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedCosts.space_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:26:05.170199+00:00
-- url     : https://prove2.me/submissions/94beb256-528d-4867-abf1-4486ca79d015

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_sourceBase_le
import Theorems.Thm_ThreeSum_LightGuardedWanted_selected_eq


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
namespace ThreeSum.EncodedColorWantedCosts
theorem _root_.solution (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    LightGuardedWanted.space free P M h J U xs ≤ space free P M h J U xs.length := by
  have h := sourceBase_le free P M h J xs
  unfold LightGuardedWanted.space LightBalancedWanted.space LightWantedSetup.space space
  rw [LightGuardedWanted.selected_eq]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl h)))
end ThreeSum.EncodedColorWantedCosts
