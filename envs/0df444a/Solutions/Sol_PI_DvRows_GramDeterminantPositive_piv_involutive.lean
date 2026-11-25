-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.piv_involutive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:09.879199+00:00
-- url     : https://prove2.me/submissions/c2a619f3-4700-45c2-b16f-af89aaf1bd82

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution : Function.Involutive (piv (K := K)) := by
  intro v
  simp only [piv]
  rcases InfinitePlace.embedding_mk_eq (v.embedding.comp (starRingEnd K)) with h1 | h1 <;> rw [h1]
  · have : (v.embedding.comp (starRingEnd K)).comp (starRingEnd K) = v.embedding := by
      ext x; simp
    rw [this, InfinitePlace.mk_embedding]
  · have : (ComplexEmbedding.conjugate (v.embedding.comp (starRingEnd K))).comp (starRingEnd K) =
        ComplexEmbedding.conjugate v.embedding := by
      ext x; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
end PI.DvRows.GramDeterminantPositive
