-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:00:57.083466+00:00
-- url     : https://prove2.me/submissions/ef7de678-3ac9-4b50-8d1e-6e154187cc54

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
theorem _root_.solution (c : ℂ) {S : A hI} {Φ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) :
    RepOn hI (c • S) (fun f => c • Φ f) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hS f hf
  refine ⟨𝓕.smul_mem c h1, ?_⟩
  show c • (S : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (c • Φ f)
  rw [h2, mk'_smul hI c h1]
end PI.QnHermHaar.Gen
