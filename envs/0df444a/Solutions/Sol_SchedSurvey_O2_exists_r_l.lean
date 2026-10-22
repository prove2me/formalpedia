-- Prove2me | solution 1 for SchedSurvey.O2.exists_r_l
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:04:34.955633+00:00
-- url     : https://prove2.me/submissions/c0220ec3-6ed7-4759-b37d-8b83723108ec

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model
set_option autoImplicit false

open SchedSurvey.O2

theorem solution {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hn : 2 ≤ n) :
    ∃ r l : Fin n, r ≠ l ∧ (∀ j ∈ setA a b, b j ≤ a r) ∧ (∀ j ∈ setB a b, a j ≤ b l) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨r0, -, hr0⟩ := Finset.exists_max_image Finset.univ a hne
  have hne' : ((Finset.univ : Finset (Fin n)).erase r0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp; omega
  by_cases h : b r0 ≤ a r0
  · obtain ⟨l, hl, hlmax⟩ := Finset.exists_max_image ((Finset.univ : Finset (Fin n)).erase r0) b hne'
    have hl0 : l ≠ r0 := (Finset.mem_erase.1 hl).1
    refine ⟨r0, l, hl0.symm, ?_, ?_⟩
    · intro j hj
      simp only [setA, Finset.mem_filter] at hj
      exact hj.2.trans (hr0 j (Finset.mem_univ _))
    · intro j hj
      simp only [setB, Finset.mem_filter] at hj
      have hj0 : j ≠ r0 := by
        rintro rfl; linarith [hj.2]
      exact hj.2.le.trans (hlmax j (Finset.mem_erase.2 ⟨hj0, Finset.mem_univ _⟩))
  · push_neg at h
    obtain ⟨r, hr, hrmax⟩ := Finset.exists_max_image ((Finset.univ : Finset (Fin n)).erase r0) a hne'
    have hr0' : r ≠ r0 := (Finset.mem_erase.1 hr).1
    refine ⟨r, r0, hr0', ?_, ?_⟩
    · intro j hj
      simp only [setA, Finset.mem_filter] at hj
      have hj0 : j ≠ r0 := by
        rintro rfl; linarith [hj.2]
      exact hj.2.trans (hrmax j (Finset.mem_erase.2 ⟨hj0, Finset.mem_univ _⟩))
    · intro j hj
      simp only [setB, Finset.mem_filter] at hj
      exact (hr0 j (Finset.mem_univ _)).trans h.le
