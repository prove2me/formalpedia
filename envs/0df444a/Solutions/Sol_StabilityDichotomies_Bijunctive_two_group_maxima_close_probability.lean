-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.two_group_maxima_close_probability
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:37:45.396665+00:00
-- url     : https://prove2.me/submissions/2d866736-220e-4bdd-abde-95ec838b9ae6

import Theorems.Thm_StabilityDichotomies_Bijunctive_two_groups_close_maxima_give_small_top_gap
import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_index_shifted_exponential_top_gap
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Bijunctive

theorem solution {α : Type} [Fintype α] (s t : Finset α)
    (hs : s.Nonempty) (ht : t.Nonempty) (hdis : Disjoint s t) (hcover : s ∪ t = Finset.univ)
    (β r : ℝ) (hβ : 0 < β) (hr : 0 ≤ r) (d : α → ℝ) :
    ((Measure.pi (fun _ : α => expMeasure β))
      {δ : α → ℝ | ∃ a ∈ s, ∃ b ∈ t,
        (∀ k ∈ s, δ k - d k ≤ δ a - d a) ∧
        (∀ k ∈ t, δ k - d k ≤ δ b - d b) ∧
        (δ a - d a) - (δ b - d b) ≤ r ∧
        (δ b - d b) - (δ a - d a) ≤ r}).toReal ≤ 1 - Real.exp (-β*r) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let μ : Measure (α → ℝ) := Measure.pi (fun _ => expMeasure β)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  obtain ⟨u,hu⟩ := hs
  obtain ⟨v,hv⟩ := ht
  have huv : u ≠ v := by
    intro h; subst v; exact Finset.disjoint_left.mp hdis hu hv
  have hcard : 2 ≤ Fintype.card α := by
    have h := Finset.card_le_univ ({u,v} : Finset α)
    simpa [Finset.card_pair huv] using h
  let E : Set (α → ℝ) := {δ | ∃ a ∈ s, ∃ b ∈ t,
        (∀ k ∈ s, δ k - d k ≤ δ a - d a) ∧
        (∀ k ∈ t, δ k - d k ≤ δ b - d b) ∧
        (δ a - d a) - (δ b - d b) ≤ r ∧
        (δ b - d b) - (δ a - d a) ≤ r}
  let G : Set (α → ℝ) := {δ | ∃ i j, i ≠ j ∧
        (∀ k, δ k - d k ≤ δ i - d i) ∧
        (∀ k, k ≠ i → δ k - d k ≤ δ j - d j) ∧
        (δ i - d i) - (δ j - d j) ≤ r}
  have hsub : E ⊆ G := by
    intro δ hδ
    obtain ⟨a,ha,b,hb,hma,hmb,hab,hba⟩ := hδ
    obtain ⟨i,hi,j,hj,hij,himax,hjmax,hgap⟩ :=
      two_groups_close_maxima_give_small_top_gap s t ⟨u,hu⟩ ⟨v,hv⟩ hdis (fun k => δ k - d k)
        a b ha hb hma hmb r hab hba
    exact ⟨i,j,hij,fun k => himax k (by rw [hcover]; exact Finset.mem_univ _),
      fun k hk => hjmax k (by rw [hcover]; exact Finset.mem_univ _) hk,hgap⟩
  have hm : (μ E).toReal ≤ (μ G).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ G) (measure_mono hsub)
  exact hm.trans (finite_index_shifted_exponential_top_gap hcard β r hβ hr d)
