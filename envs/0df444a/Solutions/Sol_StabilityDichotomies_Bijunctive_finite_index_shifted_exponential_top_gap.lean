-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_index_shifted_exponential_top_gap
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:34:06.978464+00:00
-- url     : https://prove2.me/submissions/9421484d-66cd-4273-8d92-94fdd606d069

import Theorems.Thm_StabilityDichotomies_Bijunctive_shifted_exponential_top_gap
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

private def finiteGap {α : Type} (d : α → ℝ) (t : ℝ) : Set (α → ℝ) :=
  {δ | ∃ i j, i ≠ j ∧ (∀ k, δ k - d k ≤ δ i - d i) ∧
    (∀ k, k ≠ i → δ k - d k ≤ δ j - d j) ∧
    (δ i - d i) - (δ j - d j) ≤ t}

private theorem finiteGap_measurable {α : Type} [Fintype α] (d : α → ℝ) (t : ℝ) :
    MeasurableSet (finiteGap d t) := by
  classical
  simp only [finiteGap, setOf_exists, setOf_and, setOf_forall]
  apply MeasurableSet.iUnion; intro i
  apply MeasurableSet.iUnion; intro j
  apply MeasurableSet.inter (by apply MeasurableSet.iInter; intro _; exact MeasurableSet.empty)
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter; intro k
    exact measurableSet_le ((measurable_pi_apply k).sub_const _) ((measurable_pi_apply i).sub_const _)
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter; intro k
    apply MeasurableSet.iInter; intro hk
    exact measurableSet_le ((measurable_pi_apply k).sub_const _) ((measurable_pi_apply j).sub_const _)
  · exact measurableSet_le (((measurable_pi_apply i).sub_const _).sub ((measurable_pi_apply j).sub_const _)) measurable_const

theorem solution {α : Type} [Fintype α] (hcard : 2 ≤ Fintype.card α)
    (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) (d : α → ℝ) :
    ((Measure.pi (fun _ : α => expMeasure β)) (finiteGap d t)).toReal ≤ 1 - Real.exp (-β*t) := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hmp := measurePreserving_piCongrLeft (fun _ : α => expMeasure β) e
  have hp := hmp.measure_preimage (finiteGap_measurable d t).nullMeasurableSet
  have heq : (MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) e) ⁻¹' finiteGap d t =
      finiteGap (d ∘ e) t := by
    ext δ
    simp only [mem_preimage, finiteGap, mem_setOf_eq, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply, Function.comp_apply]
    constructor
    · rintro ⟨i,j,hij,hi,hj,hg⟩
      refine ⟨e.symm i,e.symm j, ?_, ?_, ?_, ?_⟩
      · exact fun he => hij (e.symm.injective he)
      · intro k
        simpa using hi (e k)
      · intro k hk
        have hneq : e k ≠ i := fun h => hk (by simpa using congrArg e.symm h)
        simpa using hj (e k) hneq
      · simpa using hg
    · rintro ⟨i,j,hij,hi,hj,hg⟩
      refine ⟨e i,e j, ?_, ?_, ?_, ?_⟩
      · exact fun he => hij (e.injective he)
      · intro k
        simpa using hi (e.symm k)
      · intro k hk
        have hneq : e.symm k ≠ i := fun h => hk (by simpa using congrArg e h)
        simpa using hj (e.symm k) hneq
      · simpa using hg
  rw [heq] at hp
  have hh := (shifted_exponential_top_gap (Fintype.card α) hcard β t hβ ht (d ∘ e)).1
  change (Measure.pi (fun _ : Fin (Fintype.card α) => expMeasure β) (finiteGap (d ∘ e) t)).toReal ≤ _ at hh
  rw [hp] at hh
  exact hh
