-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCanonicalSourceBank.source_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:28:54.73738+00:00
-- url     : https://prove2.me/submissions/082c1920-08d8-408b-9021-6fa12fd9d0a1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_dictionary_native

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
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r))
    (original : Fin r→ZMod p)
    (hjoin : ((p^r : ℕ) : ℤ)∣(TernaryExtensionEncoding.coefficientCode original : ℤ)-
      LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map (native right maps)) p r j.val) :
    original=nativeRow right maps B j := by
  rw [dictionary_native] at hjoin
  have he := Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr hjoin)
  change TernaryExtensionEncoding.coefficientCode (nativeRow right maps B j)%(p^r)=
    TernaryExtensionEncoding.coefficientCode original%(p^r) at he
  rw [Nat.mod_eq_of_lt (TernaryExtensionEncoding.coefficientCode_lt _),
    Nat.mod_eq_of_lt (TernaryExtensionEncoding.coefficientCode_lt _)] at he
  exact (TernaryExtensionEncoding.coefficientCode_injective r he).symm
end ThreeSum.WeightedGlobalCanonicalSourceBank
