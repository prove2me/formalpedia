-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.conditional_excluded_cutoff_order_uniform
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:35:38.180287+00:00
-- url     : https://prove2.me/submissions/e7dc8a09-44fd-4118-8fb4-2ff6eb78b139

import Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_excluded_cutoff_iid_fin_law
import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_continuous_order_uniform
import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_atomless_pair_tie_null
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function StabilityDichotomies.Bijunctive

theorem solution {α : Type} [Fintype α]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (m : α → Bool)
    (n : ℕ) (e : Fin n ≃ Option {i // m i = false}) (p : Equiv.Perm (Fin n)) :
    let f := (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm) ∘
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // m i = false} => ℝ)).symm ∘
      (fun z : (α → ℝ) × ℝ => (fun i : {i // m i = false} => z.1 i, z.2))
    (ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)
      {z | ∀ i, (Finset.univ.filter (fun j : Fin n => f z j < f z i)).card = (p i).val}).toReal =
    1 / n.factorial := by
  classical
  let D := {i // m i = false}
  let Q := ProbabilityTheory.cond ((Measure.pi (fun _ : α => unitPriorityMeasure)).prod (cutoffMeasure ε))
        ((Set.univ.pi (fun i => if m i then Iic (1 - ε / 2) else Ioi (1 - ε / 2))) ×ˢ Set.univ)
  let proj : ((α → ℝ) × ℝ) → ((D → ℝ) × ℝ) := fun z => (fun i => z.1 i,z.2)
  let opt := (MeasurableEquiv.piOptionEquivProd (fun _ : Option D => ℝ)).symm
  let fin := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  let f := fin ∘ opt ∘ proj
  let E : Set (Fin n → ℝ) := {x | ∀ i, (Finset.univ.filter (fun j : Fin n => x j < x i)).card = (p i).val}
  haveI : IsProbabilityMeasure (cutoffMeasure ε) := by
    unfold cutoffMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  haveI : NullSingletonClass (cutoffMeasure ε) := by
    constructor
    intro x
    unfold cutoffMeasure ProbabilityTheory.cond
    rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
    have hz : volume ({x} ∩ Icc (1 - ε / 2) 1) = 0 := measure_mono_null Set.inter_subset_left (measure_singleton x)
    simp [hz]
  have hp : Measurable proj := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply (i : α)).comp measurable_fst
    · exact measurable_snd
  have hf : Measurable f := fin.measurable.comp (opt.measurable.comp hp)
  have hrank (i : Fin n) : Measurable (fun x : Fin n → ℝ => (Finset.univ.filter (fun j : Fin n => x j < x i)).card) := by
    have he : (fun x : Fin n → ℝ => (Finset.univ.filter (fun j : Fin n => x j < x i)).card) =
        fun x => ∑ j : Fin n, if x j < x i then (1 : ℕ) else 0 := by
      funext x
      exact Finset.card_filter _ _
    rw [he]
    apply Finset.measurable_sum
    intro j hj
    exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)) measurable_const measurable_const
  have hE : MeasurableSet E := by
    have he : E = ⋂ i : Fin n, {x | (Finset.univ.filter (fun j : Fin n => x j < x i)).card = (p i).val} := by
      ext x; simp [E]
    rw [he]
    exact MeasurableSet.iInter fun i => measurableSet_eq.preimage (hrank i)
  have hlaw : Measure.map f Q = Measure.pi (fun _ : Fin n => cutoffMeasure ε) :=
    conditional_excluded_cutoff_iid_fin_law ε hε hε1 m n e
  have hprob := iid_continuous_order_uniform n (cutoffMeasure ε)
    (fun a b hab => iid_atomless_pair_tie_null n (cutoffMeasure ε) a b hab) p
  change (Q (f ⁻¹' E)).toReal = _
  rw [← Measure.map_apply hf hE, hlaw]
  exact hprob
