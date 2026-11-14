-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.two_groups_close_maxima_give_small_top_gap
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:30:31.944207+00:00
-- url     : https://prove2.me/submissions/d5e2f1ce-ca7e-4823-a740-9d1ddeca1db7

import Mathlib
noncomputable section
open scoped Classical

theorem solution {α : Type} [DecidableEq α]
    (s t : Finset α) (hs : s.Nonempty) (ht : t.Nonempty) (hdis : Disjoint s t)
    (f : α → ℝ) (a b : α) (ha : a ∈ s) (hb : b ∈ t)
    (hamax : ∀ k ∈ s, f k ≤ f a) (hbmax : ∀ k ∈ t, f k ≤ f b)
    (r : ℝ) (hab : f a - f b ≤ r) (hba : f b - f a ≤ r) :
    ∃ i ∈ s ∪ t, ∃ j ∈ s ∪ t, i ≠ j ∧
      (∀ k ∈ s ∪ t, f k ≤ f i) ∧
      (∀ k ∈ s ∪ t, k ≠ i → f k ≤ f j) ∧
      f i - f j ≤ r := by
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image (s ∪ t) f (hs.mono Finset.subset_union_left)
  have habne : a ≠ b := by
    intro h
    subst b
    exact (Finset.disjoint_left.mp hdis ha hb)
  have herase : ((s ∪ t).erase i).Nonempty := by
    by_cases h : a = i
    · exact ⟨b, Finset.mem_erase.mpr ⟨by simpa [← h] using habne.symm, Finset.mem_union_right _ hb⟩⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨h, Finset.mem_union_left _ ha⟩⟩
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image ((s ∪ t).erase i) f herase
  have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjin : j ∈ s ∪ t := (Finset.mem_erase.mp hj).2
  refine ⟨i, hi, j, hjin, Ne.symm hjne, himax, ?_, ?_⟩
  · intro k hk hki
    exact hjmax k (Finset.mem_erase.mpr ⟨hki, hk⟩)
  · rcases Finset.mem_union.mp hi with his | hit
    · have hbi : b ≠ i := by
        intro h
        subst b
        exact Finset.disjoint_left.mp hdis his hb
      have hbj := hjmax b (Finset.mem_erase.mpr ⟨hbi, Finset.mem_union_right _ hb⟩)
      have hia := hamax i his
      linarith
    · have hai : a ≠ i := by
        intro h
        subst a
        exact Finset.disjoint_left.mp hdis ha hit
      have haj := hjmax a (Finset.mem_erase.mpr ⟨hai, Finset.mem_union_left _ ha⟩)
      have hib := hbmax i hit
      linarith
