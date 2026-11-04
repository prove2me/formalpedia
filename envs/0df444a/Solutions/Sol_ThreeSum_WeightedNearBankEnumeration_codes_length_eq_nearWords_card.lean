-- Prove2me | solution 1 for ThreeSum.WeightedNearBankEnumeration.codes_length_eq_nearWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:08.684648+00:00
-- url     : https://prove2.me/submissions/c190fd77-da83-403d-8f31-e399b59eb4b8

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_words_image_nearWords
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_injective
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_words_nodup
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_words_nodup
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length



set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)
namespace ThreeSum.WeightedNearBankEnumeration
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (WeightedNearEnumeration.codes (wordList Q) D).length = (nearWords Q D).card := by
  rw [WeightedNearEnumeration.codes_length,
    ← List.toFinset_card_of_nodup (WeightedNearEnumeration.words_nodup _ _ (wordList_digits Q)),
    words_image_nearWords]
  exact Finset.card_image_of_injective _ (wordList_injective N)
end ThreeSum.WeightedNearBankEnumeration
