-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localCorrectionComponent_invariant_radius_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:47:20.821822+00:00
-- url     : https://prove2.me/submissions/e1a8dabb-99d8-4143-8999-ca440f2f798f

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localResidual_invariant_radius_one

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
    (hcoh : LocalTopCohomologyIdentification A)
    (z : C2 i.castSucc)
    (sigma tau : D.family.Cochain2 i.succ)
    (hAgree : SignalAgreementWithin A z 1 sigma tau) :
    localCorrectionComponent A hcoh z sigma =
      localCorrectionComponent A hcoh z tau := by
  have hResidual := localResidual_invariant_radius_one A z sigma tau hAgree
  unfold localCorrectionComponent
  rw [hResidual]
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
