-- Prove2me | solution 1 for ProjSchedTW.OrderPolyhedra.resource_feasible_iff_minimal_forbidden_sets_separated
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:27:02.735069+00:00
-- url     : https://prove2.me/submissions/ca55afad-45e0-4725-9fb8-f6da41aa00b1

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

set_option autoImplicit false

open ProjSchedTW.OrderPolyhedra in
theorem d0d5aeb8_pos_of_mem_minimal {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions)
    (F : Finset (Fin (n + 2))) (hF : P.IsMinimalForbidden F) (i : Fin (n + 2)) (hi : i ∈ F) :
    0 < P.p i := by
  obtain ⟨_, _, _, hpos, _, hr0, _, _, _⟩ := hP
  by_contra hcon
  have hzero : ∀ k, P.r i k = 0 := by
    by_cases h0 : i = 0
    · subst h0; exact fun k => (hr0 k).1
    by_cases hl : i = Fin.last (n + 1)
    · subst hl; exact fun k => (hr0 k).2
    exact absurd (hpos i h0 hl) hcon
  have hforb : P.IsForbidden (F.erase i) := by
    obtain ⟨k, hk⟩ := hF.1
    refine ⟨k, ?_⟩
    rw [← Finset.add_sum_erase F _ hi, hzero k, zero_add] at hk
    exact hk
  have hle : F ≤ F.erase i := hF.2 hforb (Finset.erase_subset i F)
  exact Finset.notMem_erase i F (hle hi)

open ProjSchedTW.OrderPolyhedra in
theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions)
    (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    P.IsResourceFeasible S ↔
      ∀ F : Finset (Fin (n + 2)), P.IsMinimalForbidden F →
        ∃ i ∈ F, ∃ j ∈ F, i ≠ j ∧ S i + (P.p i : ℝ) ≤ S j := by
  constructor
  · intro hRF F hF
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := hF.1
    have hne : F.Nonempty := by
      rcases F.eq_empty_or_nonempty with h | h
      · subst h; simp at hk
      · exact h
    obtain ⟨j, hj, hjmax⟩ := F.exists_max_image S hne
    have hsub : F ⊆ P.activeSet S (S j) := by
      intro i hi
      simp only [Project.activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hjmax i hi, ?_⟩
      by_cases hij : i = j
      · subst hij
        have := d0d5aeb8_pos_of_mem_minimal P hP F hF i hi
        have : (0 : ℝ) < (P.p i : ℝ) := by exact_mod_cast this
        linarith
      · exact hcon i hi j hj hij
    have hle : ∑ i ∈ F, P.r i k ≤ P.usage S (S j) k :=
      Finset.sum_le_sum_of_subset hsub
    have := hRF (S j) (hS.2 j) k
    omega
  · intro hsep t ht k
    by_contra hcon
    push_neg at hcon
    have hforb : P.IsForbidden (P.activeSet S t) := ⟨k, hcon⟩
    obtain ⟨F, hFA, hFmin⟩ := exists_minimal_le_of_wellFoundedLT P.IsForbidden _ hforb
    obtain ⟨i, hi, j, hj, _, hij⟩ := hsep F hFmin
    have hiA := hFA hi
    have hjA := hFA hj
    simp only [Project.activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiA hjA
    linarith [hiA.2, hjA.1]
