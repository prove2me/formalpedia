-- Prove2me | solution 1 for ThreeSum.LightTernaryNearEnumerationMain.time_bank_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:03.356661+00:00
-- url     : https://prove2.me/submissions/4215bc1b-8e65-444e-8fd0-00645c29748a

import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_visits_le_nearWords


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryNearEnumerationMain
theorem _root_.solution {N : ℕ} (Q : ThreeSum.TernaryJointType.TritWord N) (D : ℕ) :
    time (ThreeSum.TernaryBankEnumeration.wordList Q) D ≤
      900*((N+1)*(ThreeSum.TernaryBank.nearWords Q D).card) :=
  Nat.mul_le_mul_left 900 (ThreeSum.TernaryNearBankEnumeration.visits_le_nearWords Q D)
end ThreeSum.LightTernaryNearEnumerationMain
