-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_coarse_graining_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:15:46.693205+00:00
-- url     : https://prove2.me/submissions/9053fd72-1ed5-4dab-9fbb-bf5ad34accbd

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_exact_relation
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarse_weight_le_input
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrectionComponent_invariant_radius_one
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_coarseSyndrome_invariant_radius_two

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
    (hcompat : InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : UpperSyndrome D i) :
    ∃ sigma' : CoarseSyndrome D i,
      ∃ correction : D.family.Cochain1 i.succ,
        correction = correctionFromSyndrome A hcoh sigma.1 ∧
        (sigma : D.family.Cochain2 i.succ) =
          D.family.coboundary1 i.succ correction +
            (D.selectedMap i).map2 sigma' ∧
        HammingWeight (sigma' : D.family.Cochain2 i.castSucc) ≤
          HammingWeight (sigma : D.family.Cochain2 i.succ) ∧
        (∀ (tau : UpperSyndrome D i) z,
          SignalAgreementWithin A z 2 sigma.1 tau.1 →
          (coarseSyndrome A hcompat sigma : D.family.Cochain2 i.castSucc) z =
            (coarseSyndrome A hcompat tau : D.family.Cochain2 i.castSucc) z) ∧
        (∀ (tau : UpperSyndrome D i) z,
          SignalAgreementWithin A z 1 sigma.1 tau.1 →
          localCorrectionComponent A hcoh z sigma.1 =
            localCorrectionComponent A hcoh z tau.1) := by
  let sigma' := coarseSyndrome A hcompat sigma
  let correction := correctionFromSyndrome A hcoh sigma.1
  refine ⟨sigma', correction, rfl, ?_, ?_, ?_, ?_⟩
  · exact rz_exact_relation A hcoh hcompat hEven sigma
  · exact coarse_weight_le_input A sigma.1
  · intro tau z hAgree
    exact coarseSyndrome_invariant_radius_two A hcompat z sigma tau hAgree
  · intro tau z hAgree
    exact localCorrectionComponent_invariant_radius_one A hcoh z sigma.1 tau.1 hAgree
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
