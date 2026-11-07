-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badBidirectionalLocalPairs_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:28:30.714784+00:00
-- url     : https://prove2.me/submissions/b9e649c7-5412-460c-b134-2ce1f888903a

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_badBidirectionalLocalPairsEncoding_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (d s m k : Nat) :
    Nat.card (badBidirectionalLocalPairs
      (F := F) (W := W) (R := R) (R' := R') d s m k) ≤
      Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badFirstImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badSecondKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badSecondImagePairs
        (F := F) (W := W) (R := R) (R' := R') d) +
      Nat.card (badForwardRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) +
      Nat.card (badReverseRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) := by
  classical
  calc
    Nat.card (badBidirectionalLocalPairs
        (F := F) (W := W) (R := R) (R' := R') d s m k) ≤
        Nat.card
          (badFirstKernelPairs
              (F := F) (W := W) (R := R) (R' := R') d ⊕
            (badFirstImagePairs
                (F := F) (W := W) (R := R) (R' := R') d ⊕
            (badSecondKernelPairs
                (F := F) (W := W) (R := R) (R' := R') d ⊕
            (badSecondImagePairs
                (F := F) (W := W) (R := R) (R' := R') d ⊕
            (badForwardRectanglePairs
                (F := F) (W := W) (R := R) (R' := R') s m k ⊕
              badReverseRectanglePairs
                (F := F) (W := W) (R := R) (R' := R') s m k))))) :=
      Nat.card_le_card_of_injective
        (badBidirectionalLocalPairsEncoding
          (F := F) (W := W) (R := R) (R' := R') d s m k)
        (badBidirectionalLocalPairsEncoding_injective
          (F := F) (W := W) (R := R) (R' := R') d s m k)
    _ = _ := by
      rw [Nat.card_sum, Nat.card_sum, Nat.card_sum, Nat.card_sum,
        Nat.card_sum]
      omega
end QEC.Coding.ProductExpansion
