-- Prove2me | solution 1 for ThreeSum.LightGuardedWanted.right_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:53.403831+00:00
-- url     : https://prove2.me/submissions/2234b15b-9f27-41c3-bdba-8242f0d882bb

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_globalKeys_bounded
import Theorems.Thm_ThreeSum_LightCoverKeyData_global_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
namespace ThreeSum.LightGuardedWanted
theorem _root_.solution (h J P : ℕ) (j : ℕ) (hj : j < totalKeys h J) :
    |right h J j| ≤ (keyBound P h J : ℤ) := by
  have hj' : j < (globalKeys h J).length := by rwa [LightCoverKeyData.global_length]
  unfold right
  rw [List.getD_eq_getElem _ _ hj']
  have hh := globalKeys_bounded h J _ (List.getElem_mem hj')
  have hb : (512*h*localPrime h)*(localPrime h+1)^J ≤ keyBound P h J := by
    unfold keyBound
    omega
  exact hh.trans (Int.ofNat_le.mpr hb)
end ThreeSum.LightGuardedWanted
