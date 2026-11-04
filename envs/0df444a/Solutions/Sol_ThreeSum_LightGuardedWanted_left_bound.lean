-- Prove2me | solution 1 for ThreeSum.LightGuardedWanted.left_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:29.425499+00:00
-- url     : https://prove2.me/submissions/fe3cef9e-4105-401a-8db9-fad12f473dbd

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Theorems.Thm_ThreeSum_RawAKeyLists_keys_bounded
import Theorems.Thm_ThreeSum_RawAKeyLists_keys_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
namespace ThreeSum.LightGuardedWanted
theorem _root_.solution {P h J : ℕ} (hP : 0 < P) (xs : List ℤ) (i : ℕ) (hi : i < 3*xs.length) :
    |left P xs i| ≤ (keyBound P h J : ℤ) := by
  have hi' : i < (RawAKeyLists.keys P xs).length := by rwa [RawAKeyLists.keys_length]
  unfold left
  rw [List.getD_eq_getElem _ _ hi']
  have hh := RawAKeyLists.keys_bounded (by exact_mod_cast hP : (0 : ℤ) < P)
    xs _ (List.getElem_mem hi')
  have hb : 2*P ≤ keyBound P h J := by unfold keyBound; omega
  exact hh.trans (by exact_mod_cast hb)
end ThreeSum.LightGuardedWanted
