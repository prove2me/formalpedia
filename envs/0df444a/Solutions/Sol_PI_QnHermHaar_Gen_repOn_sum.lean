-- Prove2me | solution 1 for PI.QnHermHaar.Gen.repOn_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:07:28.990801+00:00
-- url     : https://prove2.me/submissions/9a5ace45-a533-4fdc-92e7-18a8e8d821ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_add
import Theorems.Thm_PI_QnHermHaar_Gen_repOn_zero

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
theorem _root_.solution {γ : Type*} (s : Finset γ) {T : γ → A hI} {Φ : γ → (β → ℂ) → β → ℂ}
    (h : ∀ c ∈ s, RepOn hI (T c) (Φ c)) : RepOn hI (∑ c ∈ s, T c) (fun f => ∑ c ∈ s, Φ c f) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact repOn_zero hI
  · intro a s ha ih h
    simp only [Finset.sum_insert ha]
    exact repOn_add hI (h a (Finset.mem_insert_self a s))
      (ih fun c hc => h c (Finset.mem_insert_of_mem hc))
end PI.QnHermHaar.Gen
