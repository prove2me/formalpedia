-- Prove2me | solution 1 for PI.QnHermHaar.Gen.pr_of_repOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:00.527517+00:00
-- url     : https://prove2.me/submissions/4789c186-95bb-4105-a6c5-4f5ef66aecd1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.QnHermHaar PI.QnHermHaar.Gen
variable {α β : Type*} [MeasurableSpace α]
variable {μ : Measure α} {ι : α → β} {𝓕 : Submodule ℂ (β → ℂ)}
variable (hI : IntOn μ ι 𝓕)
variable (G : Set β) (hG : ∀ᵐ x ∂μ, ι x ∈ G)
variable {G}
variable (hG : ∀ᵐ x ∂μ, ι x ∈ G)
namespace PI.QnHermHaar.Gen
theorem _root_.solution {T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hT : RepOn hI T Φ) (hS : RepOn hI (star T) Ψ)
    {f h : β → ℂ} (hf : f ∈ 𝓕) (hh : h ∈ 𝓕) : pr μ ι (Φ f) h = pr μ ι f (Ψ h) := by
  rw [← ip_mk' hI (hT f hf).1 hh, ← (hT f hf).2, star_spec, (hS h hh).2,
    ip_mk' hI hf (hS h hh).1]
end PI.QnHermHaar.Gen
