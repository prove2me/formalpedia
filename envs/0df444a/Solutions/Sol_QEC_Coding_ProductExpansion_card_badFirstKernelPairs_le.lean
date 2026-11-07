-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badFirstKernelPairs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:26:18.491192+00:00
-- url     : https://prove2.me/submissions/c3ec9548-9bd1-4a3b-9a4b-1dbca85d3431

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_badFirstKernelPairsEncoding_injective

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
    Nat.card (badFirstKernelPairs
      (F := F) (W := W) (R := R) (R' := R') d) ≤
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) *
        Nat.card (Matrix R' W F) := by
  calc
    Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) ≤
        Nat.card
          (badChecksForDistance (F := F) (W := W) (R := R) d ×
            Matrix R' W F) :=
      Nat.card_le_card_of_injective
        (badFirstKernelPairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d)
        (badFirstKernelPairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d)
    _ = _ := by rw [Nat.card_prod]
end QEC.Coding.ProductExpansion
