-- Prove2me | solution 1 for PI.OmFibreUniq.W.dT_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:23.260086+00:00
-- url     : https://prove2.me/submissions/efd44932-49b4-4fdb-a184-be8a95ae119e

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
theorem _root_.solution (h : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) :
    (dT σ ψ v a).IsAddHaarMeasure := by
  unfold dT
  rw [dif_pos h]
  exact h.choose_spec.1
end PI.OmFibreUniq.W
