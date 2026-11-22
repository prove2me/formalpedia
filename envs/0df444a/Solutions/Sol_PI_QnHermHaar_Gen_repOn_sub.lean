-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:43.461835+00:00
-- url     : https://prove2.me/submissions/57e7f0ee-5849-41f5-adf7-165371e02430

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
theorem _root_.solution {S T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) (hT : RepOn hI T Ψ) :
    RepOn hI (S - T) (fun f => Φ f - Ψ f) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hS f hf
  obtain ⟨h3, h4⟩ := hT f hf
  refine ⟨𝓕.sub_mem h1 h3, ?_⟩
  show (S : Module.End ℂ (X hI)) (mk' hI f) - (T : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (Φ f - Ψ f)
  rw [h2, h4, mk'_sub hI h1 h3]
end PI.QnHermHaar.Gen
