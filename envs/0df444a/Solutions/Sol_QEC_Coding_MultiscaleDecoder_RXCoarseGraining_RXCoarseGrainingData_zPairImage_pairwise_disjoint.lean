-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.zPairImage_pairwise_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:08:23.071077+00:00
-- url     : https://prove2.me/submissions/d4e2d0b0-095b-48a6-931b-d9d321f96db4

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
  (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
namespace QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
theorem _root_.solution
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    Set.PairwiseDisjoint (Set.univ : Set (C2 i.castSucc)) (zPairImage A) := by
  intro z _ z' _ hne
  refine Finset.disjoint_left.2 ?_
  intro p hp hp'
  rcases Finset.mem_image.mp hp with ⟨b, -, hb⟩
  rcases Finset.mem_image.mp hp' with ⟨b', -, hb'⟩
  have hpair : (z, b) = (z', b') :=
    A.induced.zPairEquiv.injective (Subtype.ext (hb.trans hb'.symm))
  have hz : z = z' := congrArg Prod.fst hpair
  exact hne hz
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
