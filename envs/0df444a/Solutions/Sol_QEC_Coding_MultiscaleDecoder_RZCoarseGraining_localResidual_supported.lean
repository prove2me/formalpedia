-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localResidual_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:43:33.059974+00:00
-- url     : https://prove2.me/submissions/3db0aaaa-e26f-4f89-92cf-b53a7c43e418

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
    (z : C2 i.castSucc)
    (sigma : D.family.Cochain2 i.succ) :
    ∀ p, p ∉ A.coarseRegion z → localResidual A z sigma p = 0 := by
  intro p hp
  change (if p ∈ A.coarseRegion z then sigma p else 0) +
      A.lift z (topParity A sigma z) p = 0
  rw [if_neg hp, A.lift_supported z (topParity A sigma z) p hp, add_zero]
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
