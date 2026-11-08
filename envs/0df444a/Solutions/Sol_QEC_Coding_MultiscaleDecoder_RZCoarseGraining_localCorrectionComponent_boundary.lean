-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.localCorrectionComponent_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:06:43.580403+00:00
-- url     : https://prove2.me/submissions/f504169e-e6fe-421c-923c-6f7f5705971f

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrection_exists_of_syndrome

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
    ∀ p, D.family.coboundary1 i.succ (localCorrectionComponent A hcoh z sigma) p =
      localResidual A z sigma p := by
  have hex := localCorrection_exists_of_syndrome A hcoh z sigma
  unfold localCorrectionComponent localCorrectionSelector
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
