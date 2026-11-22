-- Prove2me | solution 1 for ReverseLogisticsNEBS.eq_41
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:12:54.863106+00:00
-- url     : https://prove2.me/submissions/72fe6915-e4a5-4603-a57f-b3e79afb9611

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_nebsE

set_option autoImplicit false

open ReverseLogisticsNEBS

namespace ReverseLogisticsNEBS.Eq41Proof

theorem aux_le {β : Type*} [LinearOrder β] [Zero β] {N : ℕ} (SE : Fin N → β) (y : Fin N → β)
    (hy : Monotone y) : ∀ n : ℕ, ∀ j : Fin N, N - j.val ≤ n →
      ∀ i : Fin N, j ≤ i → nebsE SE y j ≤ max (y i) (SE i) := by
  intro n
  induction n with
  | zero =>
    intro j hj
    exact absurd hj (by have := j.isLt; omega)
  | succ n ih =>
    intro j hj i hji
    rw [nebsE]
    split_ifs with h
    · rcases eq_or_lt_of_le hji with rfl | hlt
      · exact max_le_max le_rfl (min_le_left _ _)
      · have hi : (⟨j.val + 1, h⟩ : Fin N) ≤ i := by
          rw [Fin.lt_iff_val_lt_val] at hlt
          rw [Fin.le_iff_val_le_val]
          simp only
          omega
        have := ih ⟨j.val + 1, h⟩ (by show N - (j.val + 1) ≤ n; omega) i hi
        exact max_le ((hy hji).trans (le_max_left _ _)) ((min_le_right _ _).trans this)
    · have : i = j := by
        rw [Fin.le_iff_val_le_val] at hji
        ext
        have := i.isLt
        omega
      subst this
      exact le_rfl

theorem aux_ex {β : Type*} [LinearOrder β] [Zero β] {N : ℕ} (SE : Fin N → β) (y : Fin N → β) :
    ∀ n : ℕ, ∀ j : Fin N, N - j.val ≤ n →
      ∃ i : Fin N, j ≤ i ∧ max (y i) (SE i) ≤ nebsE SE y j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    exact absurd hj (by have := j.isLt; omega)
  | succ n ih =>
    intro j hj
    rw [nebsE]
    split_ifs with h
    · obtain ⟨i, hji, hi⟩ := ih ⟨j.val + 1, h⟩ (by show N - (j.val + 1) ≤ n; omega)
      rcases le_total (SE j) (nebsE SE y ⟨j.val + 1, h⟩) with hc | hc
      · exact ⟨j, le_rfl, by rw [min_eq_left hc]⟩
      · refine ⟨i, ?_, ?_⟩
        · rw [Fin.le_iff_val_le_val] at hji ⊢
          simp only at hji
          omega
        · rw [min_eq_right hc]
          exact hi.trans (le_max_right _ _)
    · exact ⟨j, le_rfl, le_rfl⟩

end ReverseLogisticsNEBS.Eq41Proof

open ReverseLogisticsNEBS.Eq41Proof in
theorem solution {β : Type*} [LinearOrder β] [Zero β] {N : ℕ} (SE : Fin N → β) (y : Fin N → β)
    (hy : Monotone y) (j : Fin N) :
    nebsE SE y j =
      (Finset.univ.filter (fun i : Fin N => j ≤ i)).inf' ⟨j, by simp⟩
        (fun i => max (y i) (SE i)) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact aux_le SE y hy (N - j.val) j le_rfl i hi
  · obtain ⟨i, hji, hi⟩ := aux_ex SE y (N - j.val) j le_rfl
    exact (Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩)).trans hi
