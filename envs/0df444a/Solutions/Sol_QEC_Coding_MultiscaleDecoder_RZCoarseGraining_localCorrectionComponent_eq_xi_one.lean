-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localCorrectionComponent_eq_xi_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:07:13.533203+00:00
-- url     : https://prove2.me/submissions/8d992462-5e80-4b43-ae28-48e767649ba1

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_sigma_agrees_xi_radius_one
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrectionComponent_invariant_radius_one

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
    (sigma : D.family.Cochain2 i.succ)
    (z : C2 i.castSucc) :
    localCorrectionComponent A hcoh z sigma =
      localCorrectionComponent A hcoh z (xiSignal A sigma z 1) := by
  exact localCorrectionComponent_invariant_radius_one A hcoh z sigma
    (xiSignal A sigma z 1) (sigma_agrees_xi_radius_one A sigma z)
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
