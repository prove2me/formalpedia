-- Prove2me | solution 1 for ThreeSum.TernaryNearBankEnumeration.codes_length_eq_nearWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:54.638274+00:00
-- url     : https://prove2.me/submissions/78704a5b-5f16-475a-b7c3-fd194109dc23

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_words_image_nearWords
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_digits
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_injective
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_words_nodup
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_words_nodup
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
namespace ThreeSum.TernaryNearBankEnumeration
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (TernaryNearEnumeration.codes (wordList Q) D).length = (nearWords Q D).card := by
  rw [TernaryNearEnumeration.codes_length,
    ← List.toFinset_card_of_nodup (TernaryNearEnumeration.words_nodup _ _ (wordList_digits Q)),
    words_image_nearWords]
  exact Finset.card_image_of_injective _ (wordList_injective N)
end ThreeSum.TernaryNearBankEnumeration
