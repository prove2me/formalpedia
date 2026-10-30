-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P39.signedNormalization
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:26:56.054805+00:00
-- url     : https://prove2.me/submissions/60899336-b2ed-4925-9225-2e5f22a11d26

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39
open QAlgorithms.Papers.Independent.Advance50.P39

theorem solution {r : ℕ} (eta : Fin r → ℝ) :
    (∑ k, eta k) = (∑ k ∈ positiveIndices eta, eta k) +
      (∑ k ∈ negativeIndices eta, eta k) ∧
    ((positiveIndices eta).Nonempty →
      0 < (∑ k ∈ positiveIndices eta, eta k) ∧
      (∑ k ∈ positiveIndices eta, normalizedContribution eta (positiveIndices eta) k) = 1 ∧
      ∀ k ∈ positiveIndices eta, 0 < normalizedContribution eta (positiveIndices eta) k ∧
        normalizedContribution eta (positiveIndices eta) k ≤ 1) ∧
    ((negativeIndices eta).Nonempty →
      (∑ k ∈ negativeIndices eta, eta k) < 0 ∧
      (∑ k ∈ negativeIndices eta, normalizedContribution eta (negativeIndices eta) k) = 1 ∧
      ∀ k ∈ negativeIndices eta, 0 < normalizedContribution eta (negativeIndices eta) k ∧
        normalizedContribution eta (negativeIndices eta) k ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold positiveIndices negativeIndices
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases lt_trichotomy (eta k) 0 with h | h | h
    · simp [h, not_lt.2 h.le]
    · simp [h]
    · simp [h, not_lt.2 h.le]
  · intro hne
    have hS : 0 < ∑ k ∈ positiveIndices eta, eta k :=
      Finset.sum_pos (fun k hk => (Finset.mem_filter.1 hk).2) hne
    refine ⟨hS, ?_, ?_⟩
    · unfold normalizedContribution
      rw [← Finset.sum_div, div_self hS.ne']
    · intro k hk
      have hk0 : 0 < eta k := (Finset.mem_filter.1 hk).2
      refine ⟨div_pos hk0 hS, ?_⟩
      unfold normalizedContribution
      rw [div_le_one hS]
      exact Finset.single_le_sum (f := eta) (fun j hj => (Finset.mem_filter.1 hj).2.le) hk
  · intro hne
    have hS : (∑ k ∈ negativeIndices eta, eta k) < 0 :=
      Finset.sum_neg (fun k hk => (Finset.mem_filter.1 hk).2) hne
    refine ⟨hS, ?_, ?_⟩
    · unfold normalizedContribution
      rw [← Finset.sum_div, div_self hS.ne]
    · intro k hk
      have hk0 : eta k < 0 := (Finset.mem_filter.1 hk).2
      refine ⟨div_pos_of_neg_of_neg hk0 hS, ?_⟩
      unfold normalizedContribution
      rw [div_le_one_of_neg hS]
      have := Finset.single_le_sum (f := fun j => -eta j)
        (fun j hj => by have := (Finset.mem_filter.1 hj).2; linarith) hk
      simp only [Finset.sum_neg_distrib] at this
      linarith
