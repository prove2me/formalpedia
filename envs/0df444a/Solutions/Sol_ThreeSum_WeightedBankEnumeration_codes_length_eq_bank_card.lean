-- Prove2me | solution 1 for ThreeSum.WeightedBankEnumeration.codes_length_eq_bank_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:50.5165+00:00
-- url     : https://prove2.me/submissions/7f78c8a1-d670-4786-85f8-a4ddafc26b6c

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_injective
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_words_image_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_words_nodup
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.WeightedAddresses.codes_length



set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
namespace ThreeSum.WeightedBankEnumeration
theorem _root_.solution (N T : ℕ) :
    (codes N T).length = (bank N T).card := by
  rw [codes_length, ← List.toFinset_card_of_nodup (words_nodup N T), words_image_bank]
  exact Finset.card_image_of_injective _ (wordList_injective N)
end ThreeSum.WeightedBankEnumeration
