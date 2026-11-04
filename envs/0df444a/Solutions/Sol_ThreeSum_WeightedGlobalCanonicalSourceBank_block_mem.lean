-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCanonicalSourceBank.block_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:05:50.952181+00:00
-- url     : https://prove2.me/submissions/736bcd4e-47c8-4091-8fb0-bd10b2177cc1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_ThreeSum_RadixKeyLists_mem_tuples
import Theorems.Thm_ThreeSum_WeightedGlobalTupleDictionaryDecode_decode_mem


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
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) (i : Fin r) :
    block right maps B j i∈records (α := fixedAlpha m) right maps B := by
  exact ((RadixKeyLists.mem_tuples _ _ _).mp (decode_mem _ _ j)).2 _ (List.getElem_mem _)
end ThreeSum.WeightedGlobalCanonicalSourceBank
