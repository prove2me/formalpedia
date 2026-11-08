-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.correction_boundary_eq_sumResidual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:09:38.011442+00:00
-- url     : https://prove2.me/submissions/dcaa9f97-ad98-4e19-9ee4-dbcca06a44b5

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_localCorrectionComponent_boundary

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
    (sigma : D.family.Cochain2 i.succ) :
    D.family.coboundary1 i.succ (correctionFromSyndrome A hcoh sigma) =
      ∑ z, localResidual A z sigma := by
  classical
  change D.family.coboundary1 i.succ
      (∑ z, localCorrectionComponent A hcoh z sigma) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  funext p
  exact localCorrectionComponent_boundary A hcoh z sigma p
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
