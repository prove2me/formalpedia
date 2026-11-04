-- Prove2me | solution 1 for ThreeSum.TernaryNearCanonical.sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:23.025803+00:00
-- url     : https://prove2.me/submissions/3815ea3f-37bf-492b-946b-d6ab53509f95

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Theorems.Thm_ThreeSum_TernaryNearCanonical_address_word
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_strictly_sorted


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryNearCanonical
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) : ∀ j k, j<k →
    k<(TernaryNearEnumeration.codes (wordList Q) D).length →
    address (word Q D j)<address (word Q D k) := by
  intro j k hj hk
  rw [address_word Q (by omega),address_word Q hk]
  exact List.pairwise_iff_getElem.mp
    (TernaryNearEnumeration.codes_strictly_sorted _ _ (wordList_digits Q)) j k (by omega) hk hj
end ThreeSum.TernaryNearCanonical
