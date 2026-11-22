-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:00:50.137649+00:00
-- url     : https://prove2.me/submissions/065ef643-81da-4e41-928b-de572b9a7c6d

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
    RepOn hI (S * T) (fun f => Φ (Ψ f)) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hT f hf
  obtain ⟨h3, h4⟩ := hS _ h1
  refine ⟨h3, ?_⟩
  show (S : Module.End ℂ (X hI)) ((T : Module.End ℂ (X hI)) (mk' hI f)) = mk' hI (Φ (Ψ f))
  rw [h2, h4]
end PI.QnHermHaar.Gen
