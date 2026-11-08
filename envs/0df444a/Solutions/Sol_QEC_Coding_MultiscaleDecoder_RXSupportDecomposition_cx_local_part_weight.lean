-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RXSupportDecomposition.cx_local_part_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:48:55.959999+00:00
-- url     : https://prove2.me/submissions/ce03a28b-e866-42c6-b2c2-48c57ea0aaea

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_HammingWeight_extend_restrict_sum

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
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
open QEC.Coding.MultiscaleDecoder.RXSupportDecomposition
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable {K : RXLocalComplexData (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz}
namespace QEC.Coding.MultiscaleDecoder.RXSupportDecomposition
theorem _root_.solution (S : RXSupportDecomposition D i K)
    (sigma : D.family.Cochain2 i.succ) :
    HammingWeight (rxLocalPart Lx sigma) =
      ∑ x : X, HammingWeight
        (restrictWordLinear (Lx.syndromeRegion x) sigma) := by
  unfold rxLocalPart
  exact HammingWeight_extend_restrict_sum
    (fun x => Lx.syndromeRegion x) S.cx_regions_pairwise_disjoint sigma
end QEC.Coding.MultiscaleDecoder.RXSupportDecomposition
