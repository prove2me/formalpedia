-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.sigma_agrees_xi_radius_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:44:31.616208+00:00
-- url     : https://prove2.me/submissions/66f03f2d-9a38-4b15-a4db-e22345a8042a

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_xiSignal_apply

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
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    SignalAgreementWithin A z 2 sigma (xiSignal A sigma z 2) := by
  intro p hp
  rw [xiSignal_apply]
  rw [if_pos hp]
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
