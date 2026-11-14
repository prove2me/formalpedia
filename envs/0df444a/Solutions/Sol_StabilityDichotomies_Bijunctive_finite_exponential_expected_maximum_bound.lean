-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_exponential_expected_maximum_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:17:32.247449+00:00
-- url     : https://prove2.me/submissions/fe421d43-78dd-43ef-9f1f-c1a5abe080ce

import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_exponential_maximum_tail_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_integrable_of_exponential_tail_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_integral_of_exponential_tail_bound
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Bijunctive

theorem solution {α : Type} [Fintype α] [Nonempty α]
    (β : ℝ) (hβ : 0 < β) :
    let μ := Measure.pi (fun _ : α => expMeasure β)
    let M := fun δ : α → ℝ => max 0 (Finset.univ.sup' Finset.univ_nonempty δ)
    Integrable M μ ∧ (∫ δ, M δ ∂μ) ≤ (Real.log (Fintype.card α) + 1) / β := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (α → ℝ) := Measure.pi (fun _ => expMeasure β)
  let M : (α → ℝ) → ℝ := fun δ => max 0 (Finset.univ.sup' Finset.univ_nonempty δ)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  have hM : Continuous M := by
    unfold M
    apply Continuous.max continuous_const
    apply Continuous.finset_sup'_apply
    intro i hi
    exact continuous_apply i
  have hnn : ∀ᵐ δ ∂μ, 0 ≤ M δ := Filter.Eventually.of_forall (fun δ => le_max_left _ _)
  have hcard : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty α)
  have ht (t : ℝ) (ht0 : 0 ≤ t) : μ.real {δ | t < M δ} ≤
      (Fintype.card α : ℝ) * Real.exp (-β*t) := by
    have he : {δ | t < M δ} = {δ : α → ℝ | ∃ i, t < δ i} := by
      ext δ
      change t < max 0 (Finset.univ.sup' Finset.univ_nonempty δ) ↔ _
      simp [lt_max_iff,not_lt_of_ge ht0, Finset.lt_sup'_iff]
    rw [he]
    exact finite_exponential_maximum_tail_bound β t hβ ht0
  have hi := integrable_of_exponential_tail_bound μ M hM.aemeasurable hnn
    (Fintype.card α) β (by positivity) hβ ht
  exact ⟨hi,integral_of_exponential_tail_bound μ M hi hnn (Fintype.card α) β hcard hβ ht⟩
