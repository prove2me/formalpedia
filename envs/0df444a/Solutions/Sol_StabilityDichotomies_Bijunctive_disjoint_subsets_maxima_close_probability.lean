-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.disjoint_subsets_maxima_close_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:42:31.70912+00:00
-- url     : https://prove2.me/submissions/76332633-cceb-4d76-8de0-be2ae58c1f32

import Theorems.Thm_StabilityDichotomies_Bijunctive_two_group_maxima_close_probability
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_independent_product_restriction
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

private def closeGroupEvent {α : Type} (s t : Finset α) (d : α → ℝ) (r : ℝ) : Set (α → ℝ) :=
  {δ | ∃ a ∈ s, ∃ b ∈ t,
    (∀ k ∈ s, δ k - d k ≤ δ a - d a) ∧
    (∀ k ∈ t, δ k - d k ≤ δ b - d b) ∧
    (δ a - d a) - (δ b - d b) ≤ r ∧ (δ b - d b) - (δ a - d a) ≤ r}

private theorem closeGroupEvent_measurable {α : Type} [Fintype α] (s t : Finset α)
    (d : α → ℝ) (r : ℝ) : MeasurableSet (closeGroupEvent s t d r) := by
  classical
  simp only [closeGroupEvent, setOf_exists, setOf_and, setOf_forall]
  apply MeasurableSet.iUnion; intro a
  apply MeasurableSet.inter (by by_cases h : a ∈ s <;> simp [h])
  apply MeasurableSet.iUnion; intro b
  apply MeasurableSet.inter (by by_cases h : b ∈ t <;> simp [h])
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter; intro k
    apply MeasurableSet.iInter; intro hk
    exact measurableSet_le ((measurable_pi_apply k).sub_const _) ((measurable_pi_apply a).sub_const _)
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter; intro k
    apply MeasurableSet.iInter; intro hk
    exact measurableSet_le ((measurable_pi_apply k).sub_const _) ((measurable_pi_apply b).sub_const _)
  apply MeasurableSet.inter
  · exact measurableSet_le (((measurable_pi_apply a).sub_const _).sub ((measurable_pi_apply b).sub_const _)) measurable_const
  · exact measurableSet_le (((measurable_pi_apply b).sub_const _).sub ((measurable_pi_apply a).sub_const _)) measurable_const

theorem solution {α : Type} [Fintype α] (s t : Finset α)
    (hs : s.Nonempty) (ht : t.Nonempty) (hdis : Disjoint s t)
    (β r : ℝ) (hβ : 0 < β) (hr : 0 ≤ r) (d : α → ℝ) :
    ((Measure.pi (fun _ : α => expMeasure β)) (closeGroupEvent s t d r)).toReal ≤
      1 - Real.exp (-β*r) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let u := s ∪ t
  letI : DecidableEq ↥u := Classical.decEq _
  let S : Finset ↥u := Finset.univ.filter (fun x => x.1 ∈ s)
  let T : Finset ↥u := Finset.univ.filter (fun x => x.1 ∈ t)
  have hS : S.Nonempty := by
    obtain ⟨a,ha⟩ := hs
    exact ⟨⟨a, Finset.mem_union_left t ha⟩, by simp [S,ha]⟩
  have hT : T.Nonempty := by
    obtain ⟨b,hb⟩ := ht
    exact ⟨⟨b, Finset.mem_union_right s hb⟩, by simp [T,hb]⟩
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    have hxs : x.1 ∈ s := (Finset.mem_filter.mp hxS).2
    have hxt : x.1 ∈ t := (Finset.mem_filter.mp hxT).2
    exact Finset.disjoint_left.mp hdis hxs hxt
  have hcover : S ∪ T = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    rcases Finset.mem_union.mp x.2 with hx | hx
    · exact Finset.mem_union_left _ (by simp [S,hx])
    · exact Finset.mem_union_right _ (by simp [T,hx])
  let d' : ↥u → ℝ := fun x => d x.1
  let E := closeGroupEvent S T d' r
  have hp : MeasurePreserving (fun x : α → ℝ => fun i : ↥u => x i)
      (Measure.pi (fun _ : α => expMeasure β)) (Measure.pi (fun _ : ↥u => expMeasure β)) :=
    finite_independent_product_restriction u (fun _ => expMeasure β)
  have heq := hp.measure_preimage (closeGroupEvent_measurable S T d' r).nullMeasurableSet
  have hsub : closeGroupEvent s t d r ⊆ (fun x : α → ℝ => fun i : ↥u => x i) ⁻¹' E := by
    intro δ hδ
    obtain ⟨a,ha,b,hb,hma,hmb,hab,hba⟩ := hδ
    let a' : ↥u := ⟨a,Finset.mem_union_left t ha⟩
    let b' : ↥u := ⟨b,Finset.mem_union_right s hb⟩
    refine ⟨a',by simp [S,a',ha],b',by simp [T,b',hb],?_,?_,hab,hba⟩
    · intro k hk
      exact hma k.1 ((Finset.mem_filter.mp hk).2)
    · intro k hk
      exact hmb k.1 ((Finset.mem_filter.mp hk).2)
  have hbound := two_group_maxima_close_probability S T hS hT hST hcover β r hβ hr d'
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : α => expMeasure β)) := by infer_instance
  have hm := ENNReal.toReal_mono (measure_ne_top (Measure.pi (fun _ : α => expMeasure β)) _) (measure_mono hsub)
  rw [heq] at hm
  exact hm.trans hbound
