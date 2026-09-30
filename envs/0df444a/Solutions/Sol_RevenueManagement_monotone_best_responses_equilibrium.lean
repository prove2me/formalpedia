-- Prove2me | solution 1 for RevenueManagement.monotone_best_responses_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:37:23.11556+00:00
-- url     : https://prove2.me/submissions/fe3b8adc-2c34-4379-b8db-40addcd6f55b

import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

/-- A monotone self-map of a nonempty finite chain `Fin m` has a fixed point. -/
lemma mbr_fixed {m : ℕ} (hm : 0 < m) (g : Fin m → Fin m) (hg : Monotone g) : ∃ i, g i = i := by
  classical
  set S := Finset.univ.filter (fun i : Fin m => i ≤ g i) with hS
  have hne : S.Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Fin.le_def]; exact Nat.zero_le _⟩⟩
  set i := S.max' hne
  have hi : i ≤ g i := (Finset.mem_filter.mp (S.max'_mem hne)).2
  have hgi : g i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg hi⟩
  exact ⟨i, le_antisymm (S.le_max' _ hgi) hi⟩

theorem mbr_main {m n : ℕ} (u1 u2 : Fin m → Fin n → ℝ) (hm : 0 < m)
    (hn : 0 < n) (h : (NoCrossing1 u1 ∧ NoCrossing2 u2) ∨ (ReverseCrossing1 u1 ∧ ReverseCrossing2 u2)) :
    ∃ i j, IsNashEquilibrium u1 u2 i j := by
  have hbr1 : ∀ j : Fin n, ∃ i, IsBestResponse1 u1 j i := by
    intro j
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => u1 i j)
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  have hbr2 : ∀ i : Fin m, ∃ j, IsBestResponse2 u2 i j := by
    intro i
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => u2 i j)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose b1 hb1 using hbr1
  choose b2 hb2 using hbr2
  have key : Monotone (fun i => b1 (b2 i)) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have m2 : Monotone b2 := by
        intro i i' hii'
        rcases eq_or_lt_of_le hii' with rfl | hlt
        · exact le_rfl
        · exact h2 i i' (b2 i) (b2 i') hlt (hb2 i) (hb2 i')
      have m1 : Monotone b1 := by
        intro j j' hjj'
        rcases eq_or_lt_of_le hjj' with rfl | hlt
        · exact le_rfl
        · exact h1 j j' (b1 j) (b1 j') hlt (hb1 j) (hb1 j')
      exact m1.comp m2
    · have a2 : Antitone b2 := by
        intro i i' hii'
        rcases eq_or_lt_of_le hii' with rfl | hlt
        · exact le_rfl
        · exact h2 i i' (b2 i) (b2 i') hlt (hb2 i) (hb2 i')
      have a1 : Antitone b1 := by
        intro j j' hjj'
        rcases eq_or_lt_of_le hjj' with rfl | hlt
        · exact le_rfl
        · exact h1 j j' (b1 j) (b1 j') hlt (hb1 j) (hb1 j')
      exact Antitone.comp a1 a2
  obtain ⟨i, hi⟩ := mbr_fixed hm _ key
  refine ⟨i, b2 i, ?_, hb2 i⟩
  have := hb1 (b2 i)
  rw [hi] at this
  exact this

end RevenueManagement

open RevenueManagement

theorem solution {m n : ℕ} (u1 u2 : Fin m → Fin n → ℝ) (hm : 0 < m)
    (hn : 0 < n) (h : (NoCrossing1 u1 ∧ NoCrossing2 u2) ∨ (ReverseCrossing1 u1 ∧ ReverseCrossing2 u2)) :
    ∃ i j, IsNashEquilibrium u1 u2 i j :=
  mbr_main u1 u2 hm hn h
