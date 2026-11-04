-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedCosts.sourceBase_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:43:52.826389+00:00
-- url     : https://prove2.me/submissions/5307e018-8a08-402b-9458-2e8a0fc8f5a8

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_ThreeSum_LightBalancedWanted_total_le_div
import Theorems.Thm_ThreeSum_LightGuardedWanted_selected_eq


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
namespace ThreeSum.EncodedColorWantedCosts
theorem _root_.solution (free P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    EncodedColorWantedData.nextFree (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J) ≤
        sourceBase free M h J xs.length := by
  have h := LightBalancedWanted.total_le_div M (LightGuardedWanted.left P xs)
    (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J)
  rw [LightGuardedWanted.selected_eq] at h
  unfold EncodedColorWantedData.nextFree sourceBase
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _
end ThreeSum.EncodedColorWantedCosts
