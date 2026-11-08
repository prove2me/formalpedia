-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.sum_localResidual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:46:29.717306+00:00
-- url     : https://prove2.me/submissions/f8ed8d09-bf06-42cc-aada-3dff78e5741f

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_sum_mask_regions

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
    (∑ z, localResidual A z sigma) =
      sigma + (D.rzMap i).map2 (topParity A sigma) := by
  classical
  calc
    (∑ z, localResidual A z sigma) =
        (∑ z, maskWord (A.coarseRegion z) sigma) +
          (∑ z, A.lift z (topParity A sigma z)) := by
      simp_rw [localResidual]
      rw [Finset.sum_add_distrib]
    _ = sigma + (D.rzMap i).map2 (topParity A sigma) := by
      rw [sum_mask_regions A sigma]
      rw [← A.induced_syndrome_decomposition (topParity A sigma)]
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
