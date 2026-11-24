-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:00:08.8458+00:00
-- url     : https://prove2.me/submissions/69bc97d6-40fd-44b3-8ba5-b6b08ed1605e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
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
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : F) :
    ∑ v : InfinitePlace F, v.embedding y = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by
  rw [trace_eq_sum_embeddings (E := ℂ)]
  refine Fintype.sum_bijective (fun v : InfinitePlace F => v.embedding.toRatAlgHom) ⟨?_, ?_⟩ _ _ ?_
  · intro v w h
    have h' : v.embedding = w.embedding := by
      have := congrArg AlgHom.toRingHom h
      simpa [RingHom.toRatAlgHom_toRingHom] using this
    rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding w, h']
  · intro σ
    refine ⟨InfinitePlace.mk (σ : F →+* ℂ), ?_⟩
    have hr : ComplexEmbedding.IsReal (σ : F →+* ℂ) :=
      InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    apply AlgHom.ext
    intro x
    show (InfinitePlace.mk (σ : F →+* ℂ)).embedding x = σ x
    rw [InfinitePlace.embedding_mk_eq_of_isReal hr]
    rfl
  · intro v
    simp
end PI.ScPsiExists.UnitaryGroupMassFormula
