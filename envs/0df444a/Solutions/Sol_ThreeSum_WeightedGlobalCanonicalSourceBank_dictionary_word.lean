-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCanonicalSourceBank.dictionary_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:17:32.595644+00:00
-- url     : https://prove2.me/submissions/1f3d9c80-9877-4e7a-a2bf-f4bf4cd1e1c9

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_ofFn_block
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalTupleCodes_canonical_code
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
    LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map wordCode) (4^fixedLength m) r j.val=
      (address (word right maps B j) : ℤ) := by
  rw [dictionary_decode,←ofFn_block]
  exact WeightedGlobalCanonicalTupleCodes.canonical_code (fun x : SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) => x.2.val) _
end ThreeSum.WeightedGlobalCanonicalSourceBank
