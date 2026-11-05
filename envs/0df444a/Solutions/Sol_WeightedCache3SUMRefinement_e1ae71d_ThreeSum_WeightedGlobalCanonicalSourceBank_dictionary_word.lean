-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalSourceBank.dictionary_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:29:36.309082+00:00
-- url     : https://prove2.me/submissions/afbd6d86-f4fa-4947-841f-358289b67206

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalSourceBank_ofFn_block
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalTupleCodes_canonical_code
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalTupleDictionaryDecode_dictionary_decode


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalSourceBank
open TernaryJointType TernaryCanonicalDictionaries WeightedGlobalRepeatedWords
open WeightedGlobalTupleDictionaryDecode TernaryCodeSemantics WeightedAddresses
open TernaryCoverLocal TernaryFixedDictionaries WeightedGlobalLocalParameters
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalSourceBank
theorem _root_.solution (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map wordCode) (4^fixedLength m) r j.val=
      (address (word right maps B j) : ℤ) := by
  rw [dictionary_decode,←ofFn_block]
  exact WeightedGlobalCanonicalTupleCodes.canonical_code (fun x : SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) => x.2.val) _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalSourceBank
