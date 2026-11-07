-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badFirstImagePairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:19.708522+00:00
-- url     : https://prove2.me/submissions/e9a2477b-fa25-451d-93d2-ed04816e4218

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_badFirstImagePairsEncoding_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
omit [DecidableEq W]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution (d : Nat) :
    Nat.card (badFirstImagePairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) *
        Nat.card (Matrix R' W F) := by
  calc
    Nat.card (badFirstImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) ≤
        Nat.card
          (badGeneratorsForDistance (F := F) (W := W) (R := R) d ×
            Matrix R' W F) :=
      Nat.card_le_card_of_injective
        (badFirstImagePairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d)
        (badFirstImagePairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d)
    _ = _ := by rw [Nat.card_prod]
end QEC.Coding.ProductExpansion
