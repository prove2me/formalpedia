-- Prove2me | solution 1 for PI.LPI.prV_mem_tensInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:48:49.567891+00:00
-- url     : https://prove2.me/submissions/9956aff9-1930-4940-89e6-03ecb16db390

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVMemTensInt
import Theorems.Thm_P2M_PI_LPI_prV_tmul__102d804e89fa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
noncomputable section
open PI PI.LPI
namespace PI.LPI
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
    prV (E := E) v s ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  have hle : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) ≤
      (tensInt (F := F) (v.adicCompletion F) (intOE E)
        (v.adicCompletionIntegers F).toSubring).comap (prV (E := E) v) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
    · change prV (E := E) v ((x : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
      rw [prV_tmul']
      exact Subring.subset_closure (Or.inl ⟨x, rfl⟩)
    · change prV (E := E) v ((1 : E) ⊗ₜ[F] (a : FiniteAdeleRing (𝓞 F) F)) ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
      rw [prV_tmul']
      exact Subring.subset_closure (Or.inr ⟨⟨(a : FiniteAdeleRing (𝓞 F) F) v, a.2 v⟩, rfl⟩)
  exact hle hs
end PI.LPI
