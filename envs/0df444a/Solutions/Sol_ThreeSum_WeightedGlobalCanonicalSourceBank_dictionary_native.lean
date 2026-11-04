-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCanonicalSourceBank.dictionary_native
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:17:35.901193+00:00
-- url     : https://prove2.me/submissions/2be2352a-a53b-463d-b675-77edff27b67a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_ofFn_block
import Theorems.Thm_ThreeSum_WeightedGlobalNativeTupleWitness_positional_ofFn
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_dictionary_decode


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
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map (native right maps)) p r j.val=
      (TernaryExtensionEncoding.coefficientCode (nativeRow right maps B j) : ℤ) := by
  rw [dictionary_decode,←ofFn_block]
  apply WeightedGlobalNativeTupleWitness.positional_ofFn
  intro i
  rfl
end ThreeSum.WeightedGlobalCanonicalSourceBank
