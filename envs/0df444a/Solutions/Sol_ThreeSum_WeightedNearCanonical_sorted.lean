-- Prove2me | solution 1 for ThreeSum.WeightedNearCanonical.sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:23:32.711044+00:00
-- url     : https://prove2.me/submissions/9e35de4b-5710-4d60-8003-9f63985c054e

import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_NearCanonical
import Theorems.Thm_ThreeSum_WeightedNearCanonical_address_word
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_strictly_sorted
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_strictly_sorted
import Theorems.Thm_ThreeSum_WeightedBankCanonical_address_word
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_strictly_sorted


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedNearBankEnumeration ThreeSum.WeightedBankEnumeration
open ThreeSum.TernaryBank (Below)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedNearCanonical
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) : ∀ j k, j<k →
    k<(WeightedNearEnumeration.codes (wordList Q) D).length →
    address (word Q D j)<address (word Q D k) := by
  intro j k hj hk
  rw [address_word Q (by omega),address_word Q hk]
  exact List.pairwise_iff_getElem.mp
    (WeightedNearEnumeration.codes_strictly_sorted _ _ (wordList_digits Q)) j k (by omega) hk hj
end ThreeSum.WeightedNearCanonical
