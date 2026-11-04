-- Prove2me | solution 1 for ThreeSum.LightGuardedWanted.selected_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:49.291834+00:00
-- url     : https://prove2.me/submissions/d6da79e7-c410-4079-b2ec-ff4cbc2e4dec

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Theorems.Thm_ThreeSum_LightCoverKeyData_global_length
import Theorems.Thm_ThreeSum_RawAKeyLists_keys_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
namespace ThreeSum.LightGuardedWanted
theorem _root_.solution (P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    LightOriginalOffset.selected M (left P xs) (right h J) (3*xs.length) (totalKeys h J)=
      RawAKeyLists.selected M P xs h J := by
  unfold RawAKeyLists.selected GlobalKeyOffset.selected
  rw [RawAKeyLists.keys_length,LightCoverKeyData.global_length]
  rfl
end ThreeSum.LightGuardedWanted
