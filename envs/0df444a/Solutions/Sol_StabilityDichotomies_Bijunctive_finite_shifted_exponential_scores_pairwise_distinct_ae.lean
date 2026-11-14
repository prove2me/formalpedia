-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_shifted_exponential_scores_pairwise_distinct_ae
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:10:36.71159+00:00
-- url     : https://prove2.me/submissions/997d46e7-79ce-4ac6-a55f-123631517473

import Theorems.Thm_StabilityDichotomies_Bijunctive_shifted_exponential_pair_tie_null
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem solution {α : Type} [Fintype α]
    (β : ℝ) (hβ : 0 < β) (d : α → ℝ) :
    ∀ᵐ x ∂(Measure.pi (fun _ : α => expMeasure β)),
      ∀ a b, a ≠ b → x a - d a ≠ x b - d b := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (α → ℝ) := Measure.pi (fun _ => expMeasure β)
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hpair (a b : α) (hab : a ≠ b) : μ {x | x a - d a = x b - d b} = 0 := by
    let z : Fin (Fintype.card α) → ℝ := d ∘ e
    let B : Set (Fin (Fintype.card α) → ℝ) := {x | x (e.symm a) - z (e.symm a) = x (e.symm b) - z (e.symm b)}
    have hBm : MeasurableSet B := measurableSet_eq_fun
      ((measurable_pi_apply (e.symm a)).sub_const _) ((measurable_pi_apply (e.symm b)).sub_const _)
    have hmp := measurePreserving_piCongrLeft (fun _ : α => expMeasure β) e
    have hAE : (MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) e) ⁻¹'
        {x : α → ℝ | x a - d a = x b - d b} = B := by
      ext x
      simp only [mem_preimage,mem_setOf_eq,MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply,eq_rec_constant,B,z,Function.comp_apply,Equiv.apply_symm_apply]
    have hE : MeasurableSet {x : α → ℝ | x a - d a = x b - d b} := measurableSet_eq_fun
      ((measurable_pi_apply a).sub_const _) ((measurable_pi_apply b).sub_const _)
    have hp := hmp.measure_preimage hE.nullMeasurableSet
    rw [hAE] at hp
    have hab' : e.symm a ≠ e.symm b := fun h => hab (e.symm.injective h)
    have hh := shifted_exponential_pair_tie_null (Fintype.card α) β hβ z (e.symm a) (e.symm b) hab'
    change (Measure.pi (fun _ : Fin (Fintype.card α) => expMeasure β)) B = 0 at hh
    rw [hh] at hp
    exact hp.symm
  apply ae_all_iff.mpr; intro a
  apply ae_all_iff.mpr; intro b
  by_cases hab : a = b
  · simp [hab]
  · have hh : ∀ᵐ x ∂μ, x a - d a ≠ x b - d b := by
      rw [ae_iff]
      have he : {x : α → ℝ | ¬(x a - d a ≠ x b - d b)} = {x | x a - d a = x b - d b} := by ext x; simp
      rw [he]
      exact hpair a b hab
    filter_upwards [hh] with x hx _
    exact hx
