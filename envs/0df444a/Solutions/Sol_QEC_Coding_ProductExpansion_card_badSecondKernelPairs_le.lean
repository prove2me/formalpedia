-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badSecondKernelPairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:24.274289+00:00
-- url     : https://prove2.me/submissions/8b160d84-9b18-4d8a-bcc2-3cfbd532dee1

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_badSecondKernelPairsEncoding_injective

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
    Nat.card (badSecondKernelPairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (Matrix R W F) *
        Nat.card (badChecksForDistance (F := F) (W := W) (R := R') d) := by
  calc
    Nat.card (badSecondKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) ≤
        Nat.card
          (Matrix R W F ×
            badChecksForDistance (F := F) (W := W) (R := R') d) :=
      Nat.card_le_card_of_injective
        (badSecondKernelPairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d)
        (badSecondKernelPairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d)
    _ = _ := by rw [Nat.card_prod]
end QEC.Coding.ProductExpansion
