-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.HammingWeight_add_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:42:30.303512+00:00
-- url     : https://prove2.me/submissions/2bae8d15-79c4-471d-a027-e7f73c85cfbe

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_hammingSupport_add_of_disjoint

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a b c
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
namespace QEC.Coding.MultiscaleDecoder
theorem _root_.solution
    {F : Type u} {ι : Type v} [AddGroup F] [DecidableEq F] [Fintype ι]
    [DecidableEq ι]
    (x y : Word F ι)
    (hxy : Disjoint (hammingSupport x) (hammingSupport y)) :
    HammingWeight (x + y) = HammingWeight x + HammingWeight y := by
  rw [HammingWeight_eq_card_hammingSupport,
    hammingSupport_add_of_disjoint x y hxy,
    Finset.card_union_of_disjoint hxy,
    ← HammingWeight_eq_card_hammingSupport x,
    ← HammingWeight_eq_card_hammingSupport y]
end QEC.Coding.MultiscaleDecoder
