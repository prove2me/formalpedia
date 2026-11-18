-- Prove2me | solution 1 for ShapleyNV.shapley_two_by_two
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:30:58.818924+00:00
-- url     : https://prove2.me/submissions/0282ace0-8a25-40c7-a44f-28868448f4f0

import Mathlib

open MeasureTheory NNReal ENNReal

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (M : ι → κ → ℝ)
    (h2 : ∀ (i i' : ι) (k k' : κ),
      min (max (M i k) (M i' k)) (max (M i k') (M i' k')) =
        max (min (M i k) (M i k')) (min (M i' k) (M i' k'))) :
    Finset.univ.inf' Finset.univ_nonempty (fun k => Finset.univ.sup' Finset.univ_nonempty (fun i => M i k)) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => Finset.univ.inf' Finset.univ_nonempty (fun k => M i k)) := by
  classical
  set U := Finset.univ.inf' Finset.univ_nonempty
    (fun k => Finset.univ.sup' Finset.univ_nonempty (fun i => M i k)) with hU
  apply le_antisymm
  · -- U ≤ L : find a row all of whose entries are ≥ U
    let S : ι → Finset κ := fun i => Finset.univ.filter (fun k => U ≤ M i k)
    have hcomp : ∀ i i', S i ⊆ S i' ∨ S i' ⊆ S i := by
      intro i i'
      by_contra hcon
      obtain ⟨hn1, hn2⟩ := not_or.1 hcon
      rw [Finset.not_subset] at hn1 hn2
      obtain ⟨k, hk, hk'⟩ := hn1
      obtain ⟨k', hk2, hk2'⟩ := hn2
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk' hk2 hk2'
      -- k : U ≤ M i k, ¬ U ≤ M i' k ; k' : U ≤ M i' k', ¬ U ≤ M i k'
      have hkk := h2 i i' k k'
      have hL : U ≤ min (max (M i k) (M i' k)) (max (M i k') (M i' k')) :=
        le_min (le_max_of_le_left hk) (le_max_of_le_right hk2)
      have hR : max (min (M i k) (M i k')) (min (M i' k) (M i' k')) < U :=
        max_lt (lt_of_le_of_lt (min_le_right _ _) (not_le.1 hk2'))
          (lt_of_le_of_lt (min_le_left _ _) (not_le.1 hk'))
      rw [hkk] at hL
      exact absurd hL (not_le.2 hR)
    obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => (S i).card)
      Finset.univ_nonempty
    have hall : ∀ k, U ≤ M i0 k := by
      intro k
      have hle : U ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => M i k) :=
        Finset.inf'_le _ (Finset.mem_univ k)
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => M i k)
      rw [hi] at hle
      have hkS : k ∈ S i := by simp [S, hle]
      rcases hcomp i i0 with h | h
      · have := h hkS
        simpa [S] using this
      · have heq : S i0 = S i :=
          Finset.eq_of_subset_of_card_le h (hi0 i (Finset.mem_univ i))
        rw [← heq] at hkS
        simpa [S] using hkS
    calc U ≤ Finset.univ.inf' Finset.univ_nonempty (fun k => M i0 k) :=
          Finset.le_inf' _ _ (fun k _ => hall k)
      _ ≤ _ := Finset.le_sup' (fun i => Finset.univ.inf' Finset.univ_nonempty (fun k => M i k))
          (Finset.mem_univ i0)
  · -- L ≤ U
    apply Finset.sup'_le
    intro i _
    apply Finset.le_inf'
    intro k _
    calc Finset.univ.inf' Finset.univ_nonempty (fun k => M i k) ≤ M i k :=
          Finset.inf'_le _ (Finset.mem_univ k)
      _ ≤ _ := Finset.le_sup' (fun i => M i k) (Finset.mem_univ i)
