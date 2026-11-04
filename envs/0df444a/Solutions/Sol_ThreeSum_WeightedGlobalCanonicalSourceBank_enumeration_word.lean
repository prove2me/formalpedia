-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCanonicalSourceBank.enumeration_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:42:19.479633+00:00
-- url     : https://prove2.me/submissions/11df57ac-4559-4f2d-9d69-f79f05a01b16

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_index_spec
import Theorems.Thm_ThreeSum_TernaryBankStageModel_index_spec
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_injective
import Theorems.Thm_ThreeSum_WeightedBankStageModel_index_spec


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalSourceBank
open TernaryJointType TernaryCanonicalDictionaries WeightedGlobalRepeatedWords
open WeightedGlobalTupleDictionaryDecode TernaryCodeSemantics WeightedAddresses
open TernaryCoverLocal TernaryFixedDictionaries WeightedGlobalLocalParameters
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalCanonicalSourceBank
theorem _root_.solution {N T : ℕ} (Eword : ℕ→TritWord N)
    (hE : ∀ k<(codes N T).length, address (Eword k)=(codes N T).getD k 0)
    (w : TritWord N) (hw : WeightedGlobalBank.cacheCost w≤T) :
    Eword ((codes N T).idxOf (address w))=w := by
  apply address_injective N
  rw [hE _ (index_spec w hw).1,(index_spec w hw).2]
end ThreeSum.WeightedGlobalCanonicalSourceBank
