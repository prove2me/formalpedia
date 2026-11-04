-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCanonicalSourceBank.block_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:19:13.13534+00:00
-- url     : https://prove2.me/submissions/28376d4a-6301-45b4-b7b7-70b74c440b69

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_ofFn_block
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalSourceBank
open TernaryJointType TernaryCanonicalDictionaries WeightedGlobalRepeatedWords
open WeightedGlobalTupleDictionaryDecode TernaryCodeSemantics WeightedAddresses
open TernaryCoverLocal TernaryFixedDictionaries WeightedGlobalLocalParameters
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalCanonicalSourceBank
theorem _root_.solution (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p) (B : ℕ) :
    Function.Injective (block (r := r) right maps B) := by
  intro i j he
  apply decode_injective _ (records_nodup right maps B) r
  rw [←ofFn_block right maps B i,←ofFn_block right maps B j,he]
end ThreeSum.WeightedGlobalCanonicalSourceBank
