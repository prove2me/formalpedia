-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.activeRegion_pairwiseDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:43:57.043032+00:00
-- url     : https://prove2.me/submissions/8bd4ef6c-4b24-4259-ad30-0b68585ad83c

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
open RZCoarseGrainingData
namespace QEC.Coding.MultiscaleDecoder.RZCoarseGraining
theorem _root_.solution
    (A : RZCoarseGrainingData D i V)
    (sigma : D.family.Cochain2 i.succ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (C2 i.castSucc)))
      (activeRegion A sigma) := by
  intro z hz z' hz' hne
  change Disjoint (activeRegion A sigma z) (activeRegion A sigma z')
  rw [Finset.disjoint_left]
  intro p hp hp'
  exact Finset.disjoint_left.1 (A.coarseRegion_disjoint z z' hne)
    (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp').1
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
