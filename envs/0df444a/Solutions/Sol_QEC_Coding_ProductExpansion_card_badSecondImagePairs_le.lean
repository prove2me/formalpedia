-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badSecondImagePairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:25.248932+00:00
-- url     : https://prove2.me/submissions/1ce1ce5f-5dbb-47cc-9217-fac49d48f3a4

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_badSecondImagePairsEncoding_injective

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
    Nat.card (badSecondImagePairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (Matrix R W F) *
        Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R') d) := by
  calc
    Nat.card (badSecondImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) ≤
        Nat.card
          (Matrix R W F ×
            badGeneratorsForDistance (F := F) (W := W) (R := R') d) :=
      Nat.card_le_card_of_injective
        (badSecondImagePairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d)
        (badSecondImagePairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d)
    _ = _ := by rw [Nat.card_prod]
end QEC.Coding.ProductExpansion
