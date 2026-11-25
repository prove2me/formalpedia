-- Prove2me | solution 1 for PI.VolStabW.exists_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:55.345496+00:00
-- url     : https://prove2.me/submissions/1dd86346-6c06-4248-9b13-063d6135022d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Theorems.Thm_PI_VolStabW_sigma_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.VolStabW
theorem _root_.solution (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hinv := sigma_invol σ hCM.2.2.2
  have hne : ∃ e, σ e ≠ e := by
    by_contra h
    push Not at h
    let w : InfinitePlace E := Classical.arbitrary _
    have hc : w.IsComplex := hCM.2.1.isComplex w
    apply (InfinitePlace.not_isReal_iff_isComplex.2 hc)
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    have := hCM.2.2.2 w.embedding x
    rw [h x] at this
    rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]
    exact this.symm
  obtain ⟨e, he⟩ := hne
  refine ⟨e - σ e, sub_ne_zero.2 (Ne.symm he), ?_⟩
  rw [map_sub, hinv]; ring
end PI.VolStabW
