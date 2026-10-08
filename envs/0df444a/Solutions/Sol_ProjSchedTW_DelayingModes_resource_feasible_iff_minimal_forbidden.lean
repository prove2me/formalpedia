-- Prove2me | solution 1 for ProjSchedTW.DelayingModes.resource_feasible_iff_minimal_forbidden
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:01:28.749925+00:00
-- url     : https://prove2.me/submissions/9a2e155a-88e1-4c58-82d7-0f49050580a3

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

set_option autoImplicit false

open ProjSchedTW.DelayingModes in
/-- In a minimal forbidden set every activity has positive duration. -/
theorem a81bf918_pos_of_mem {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) (F : Finset (Fin (n + 2)))
    (hF : P.IsMinimalForbidden F) (i : Fin (n + 2)) (hi : i ∈ F) : 0 < P.p i := by
  obtain ⟨_, _, _, hpos, _, hr0, _, _, _⟩ := hP
  apply hpos
  · rintro rfl
    obtain ⟨k, hk⟩ := hF.1
    have hsub : F.erase 0 ≤ F := Finset.erase_subset _ _
    have hforb : P.IsForbidden (F.erase 0) := by
      refine ⟨k, ?_⟩
      rw [← Finset.add_sum_erase F _ hi, (hr0 k).1, zero_add] at hk
      exact hk
    have := hF.2 hforb hsub
    exact (Finset.notMem_erase 0 F) (this hi)
  · rintro rfl
    obtain ⟨k, hk⟩ := hF.1
    have hsub : F.erase (Fin.last (n + 1)) ≤ F := Finset.erase_subset _ _
    have hforb : P.IsForbidden (F.erase (Fin.last (n + 1))) := by
      refine ⟨k, ?_⟩
      rw [← Finset.add_sum_erase F _ hi, (hr0 k).2, zero_add] at hk
      exact hk
    have := hF.2 hforb hsub
    exact (Finset.notMem_erase _ F) (this hi)

open ProjSchedTW.DelayingModes in
theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    P.IsResourceFeasible S ↔
      ∀ F : Finset (Fin (n + 2)), P.IsMinimalForbidden F →
        ∃ i ∈ F, ∃ j ∈ F, i ≠ j ∧ S i + P.p i ≤ S j := by
  constructor
  · rintro ⟨_, hfeas⟩ F hF
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := hF.1
    have hne : F.Nonempty := by
      rcases F.eq_empty_or_nonempty with h | h
      · subst h; simp at hk
      · exact h
    obtain ⟨m, hm, hmax⟩ := F.exists_max_image S hne
    have hsub : F ⊆ P.activeSet S (S m) := by
      intro i hi
      simp only [Project.activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hmax i hi, ?_⟩
      by_cases him : i = m
      · subst him
        have := a81bf918_pos_of_mem P hP F hF i hi
        have : (0 : ℝ) < P.p i := by exact_mod_cast this
        linarith
      · exact hcon i hi m hm him
    have h1 := hfeas (S m) (hS.2 m) k
    have h2 : ∑ i ∈ F, P.r i k ≤ P.usage S k (S m) :=
      Finset.sum_le_sum_of_subset hsub
    omega
  · intro h
    refine ⟨hS, ?_⟩
    intro t _ k
    by_contra hlt
    push_neg at hlt
    have hforb : P.IsForbidden (P.activeSet S t) := ⟨k, hlt⟩
    obtain ⟨F, hFle, hFmin⟩ := exists_minimal_le_of_wellFoundedLT P.IsForbidden _ hforb
    obtain ⟨i, hi, j, hj, _, hij⟩ := h F hFmin
    have hi' := hFle hi
    have hj' := hFle hj
    simp only [Project.activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
    linarith [hi'.2, hj'.1]
