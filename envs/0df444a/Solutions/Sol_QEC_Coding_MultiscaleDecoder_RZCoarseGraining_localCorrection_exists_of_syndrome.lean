-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localCorrection_exists_of_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:47:43.879081+00:00
-- url     : https://prove2.me/submissions/95f02c65-7e26-4168-8367-557f2a397c20

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrection_exists
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localResidual_supported
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localResidual_parity_zero

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
    (sigma : D.family.Cochain2 i.succ) :
    ∃ f : D.family.Cochain1 i.succ,
      (∀ q, q ∉ A.correctionRegion z → f q = 0) ∧
        (∀ p, D.family.coboundary1 i.succ f p = localResidual A z sigma p) := by
  exact localCorrection_exists A hcoh z (localResidual A z sigma)
    (localResidual_supported A z sigma) (localResidual_parity_zero A z sigma)
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
