-- Prove2me | solution 1 for ThreeSum.TernaryBankEnumeration.codes_length_eq_bank_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:12:44.088688+00:00
-- url     : https://prove2.me/submissions/c6af63c3-be6b-46d0-bfc4-9041c09899a6

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_injective
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_words_image_bank
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_words_nodup
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
attribute [local simp] ThreeSum.TernaryAddresses.codes_length



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryBankEnumeration
theorem _root_.solution (N T : ℕ) :
    (codes N T).length = (bank N T).card := by
  rw [codes_length, ← List.toFinset_card_of_nodup (words_nodup N T), words_image_bank]
  exact Finset.card_image_of_injective _ (wordList_injective N)
end ThreeSum.TernaryBankEnumeration
