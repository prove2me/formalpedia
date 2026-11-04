-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCanonicalSourceBank.address_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:06:17.485601+00:00
-- url     : https://prove2.me/submissions/50f7bf97-25bf-4887-bcac-779422af083b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_mem_words
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_eq_map
import Theorems.Thm_ThreeSum_WeightedAddresses_code_eq_original
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_mem_words
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_eq_map
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalSourceBank
open TernaryJointType TernaryCanonicalDictionaries WeightedGlobalRepeatedWords
open WeightedGlobalTupleDictionaryDecode TernaryCodeSemantics WeightedAddresses
open TernaryCoverLocal TernaryFixedDictionaries WeightedGlobalLocalParameters
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalCanonicalSourceBank
theorem _root_.solution {N T : ℕ} (w : TritWord N) (hw : WeightedGlobalBank.cacheCost w≤T) :
    address w∈codes N T := by
  rw [codes_eq_map]
  refine List.mem_map.mpr ⟨WeightedBankEnumeration.wordList w,
    (WeightedBankEnumeration.wordList_mem_words w).mpr (WeightedGlobalBank.mem_bank.mpr hw),?_⟩
  rw [WeightedAddresses.code_eq_original]
  rfl
end ThreeSum.WeightedGlobalCanonicalSourceBank
