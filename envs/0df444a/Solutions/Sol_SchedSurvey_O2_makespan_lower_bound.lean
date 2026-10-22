-- Prove2me | solution 1 for SchedSurvey.O2.makespan_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:05:18.551712+00:00
-- url     : https://prove2.me/submissions/c4afac40-7068-4599-a6db-8f7305b74f5d

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model
set_option autoImplicit false

open SchedSurvey.O2 MeasureTheory

lemma oo_sum_le {n : ℕ} (s p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∀ j, 0 ≤ s j) (T : ℝ)
    (hT : 0 ≤ T) (hc : ∀ j, s j + p j ≤ T)
    (hno : ∀ j k, j ≠ k → NoOverlap (s j) (p j) (s k) (p k)) :
    ∑ j, p j ≤ T := by
  have hdisj : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun j => Set.Ico (s j) (s j + p j)) := by
    intro j _ k _ hjk
    rw [Function.onFun, Set.disjoint_left]
    intro x hxj hxk
    rcases hno j k hjk with h | h
    · simp only [Set.mem_Ico] at hxj hxk; linarith [hxj.2, hxk.1]
    · simp only [Set.mem_Ico] at hxj hxk; linarith [hxj.1, hxk.2]
  have h1 := measure_biUnion_finset (μ := volume) hdisj (fun j _ => measurableSet_Ico)
  have hsub : (⋃ j ∈ (Finset.univ : Finset (Fin n)), Set.Ico (s j) (s j + p j)) ⊆ Set.Icc 0 T := by
    intro x hx
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_Ico] at hx
    obtain ⟨j, h1, h2⟩ := hx
    exact ⟨(hs j).trans h1, (h2.trans_le (hc j)).le⟩
  have h2 := measure_mono (μ := volume) hsub
  rw [h1] at h2
  simp only [Real.volume_Ico, Real.volume_Icc, add_sub_cancel_left, sub_zero] at h2
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp j)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hT).1 h2

theorem solution {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (S : Schedule n) (hS : IsFeasible a b S) (T : ℝ) (hT : 0 ≤ T)
    (hST : CompletesBy a b S T) :
    T₁ a ≤ T ∧ T₂ b ≤ T ∧ ∀ j, a j + b j ≤ T := by
  obtain ⟨h0, h1, h2, h3⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · exact oo_sum_le S.s₁ a ha (fun j => (h0 j (Finset.mem_univ _)).1) T hT (fun j => (hST j).1)
      (fun j k hjk => h1 j (Finset.mem_univ _) k (Finset.mem_univ _) hjk)
  · exact oo_sum_le S.s₂ b hb (fun j => (h0 j (Finset.mem_univ _)).2) T hT (fun j => (hST j).2)
      (fun j k hjk => h2 j (Finset.mem_univ _) k (Finset.mem_univ _) hjk)
  · intro j
    have := h3 j (Finset.mem_univ _)
    have e1 := (hST j).1
    have e2 := (hST j).2
    have n1 := (h0 j (Finset.mem_univ _)).1
    have n2 := (h0 j (Finset.mem_univ _)).2
    rcases this with h | h <;> linarith
