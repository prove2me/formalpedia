-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:39.799394+00:00
-- url     : https://prove2.me/submissions/685a02bf-d44b-4cfc-9b11-29f6946df229

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
import Theorems.Thm_P2M_PI_QnHermHaar_Gen_mk__neg_9a326db1785f

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
theorem _root_.solution {S : A hI} {Φ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) :
    RepOn hI (-S) (fun f => -Φ f) := by
  intro f hf
  obtain ⟨h1, h2⟩ := hS f hf
  refine ⟨𝓕.neg_mem h1, ?_⟩
  show -(S : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (-Φ f)
  rw [h2, mk'_neg hI h1]
end PI.QnHermHaar.Gen
