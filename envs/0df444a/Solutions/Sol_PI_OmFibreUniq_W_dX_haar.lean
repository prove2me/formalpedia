-- Prove2me | solution 1 for PI.OmFibreUniq.W.dX_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:29.356259+00:00
-- url     : https://prove2.me/submissions/a1bc7153-d6b9-4e73-9f41-0af10fe50bb6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OmFibreUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq
open scoped TensorProduct Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
namespace PI.OmFibreUniq.W
theorem _root_.solution (h : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) :
    (dX σ J ψ v a).IsAddHaarMeasure := by
  unfold dX
  rw [dif_pos h]
  exact h.choose_spec.1
end PI.OmFibreUniq.W
