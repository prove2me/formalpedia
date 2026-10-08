-- Prove2me | solution 1 for ProjSchedTW.DelayingModes.minimal_delaying_alternative_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:17:29.984889+00:00
-- url     : https://prove2.me/submissions/0eadb15e-56a6-4452-806a-a8ff9c1c9bb0

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

set_option autoImplicit false

open ProjSchedTW.DelayingModes in
theorem feasibleSet_iff_7bdd46e5 {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (A : Finset (Fin (n + 2))) :
    P.IsFeasibleSet A ↔ ∀ k : K, ∑ i ∈ A, P.r i k ≤ P.R k := by
  unfold Project.IsFeasibleSet Project.IsForbidden
  push_neg
  rfl

open ProjSchedTW.DelayingModes in
theorem solution {n : ℕ} {K : Type} [Fintype K] (P : Project n K)
    (hP : P.StandingAssumptions) (F B : Finset (Fin (n + 2))) (hF : P.IsForbidden F) :
    (P.IsMinimalDelayingAlternative F B ↔
        B ⊆ F ∧ Maximal (fun A : Finset (Fin (n + 2)) => A ⊆ F ∧ P.IsFeasibleSet A) (F \ B)) ∧
      (P.IsMinimalDelayingAlternative F B ↔
        B ⊆ F ∧ (∀ k : K, ∑ i ∈ F \ B, P.r i k ≤ P.R k) ∧
          (∀ j ∈ B, ∃ k : K, P.R k < ∑ i ∈ F \ B, P.r i k + P.r j k)) := by
  classical
  constructor
  · constructor
    · rintro ⟨⟨hBF, hfeas⟩, hmin⟩
      refine ⟨hBF, ⟨Finset.sdiff_subset, hfeas⟩, ?_⟩
      rintro A ⟨hAF, hAfeas⟩ hle
      have hB' : P.IsDelayingAlternative F (F \ A) := by
        refine ⟨Finset.sdiff_subset, ?_⟩
        rwa [Finset.sdiff_sdiff_eq_self hAF]
      have hsub : F \ A ≤ B := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        by_contra hxB
        exact hx.2 (hle (Finset.mem_sdiff.2 ⟨hx.1, hxB⟩))
      have h2 := hmin hB' hsub
      intro x hx
      refine Finset.mem_sdiff.2 ⟨hAF hx, fun hxB => ?_⟩
      have := h2 hxB
      exact (Finset.mem_sdiff.1 this).2 hx
    · rintro ⟨hBF, ⟨-, hfeas⟩, hmax⟩
      refine ⟨⟨hBF, hfeas⟩, ?_⟩
      rintro B' ⟨hB'F, hB'feas⟩ hB'B
      have hle : F \ B ≤ F \ B' := Finset.sdiff_subset_sdiff (le_refl F) hB'B
      have h2 := hmax ⟨Finset.sdiff_subset, hB'feas⟩ hle
      intro x hxB
      by_contra hxB'
      have hx : x ∈ F \ B' := Finset.mem_sdiff.2 ⟨hBF hxB, hxB'⟩
      exact (Finset.mem_sdiff.1 (h2 hx)).2 hxB
  · constructor
    · rintro ⟨⟨hBF, hfeas⟩, hmin⟩
      refine ⟨hBF, (feasibleSet_iff_7bdd46e5 P _).1 hfeas, ?_⟩
      intro j hj
      by_contra hcon
      push_neg at hcon
      have hB' : P.IsDelayingAlternative F (B.erase j) := by
        refine ⟨(Finset.erase_subset j B).trans hBF, ?_⟩
        rw [feasibleSet_iff_7bdd46e5]
        intro k
        have heq : F \ B.erase j = insert j (F \ B) := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
          constructor
          · rintro ⟨hxF, hx⟩
            by_cases hxj : x = j
            · exact Or.inl hxj
            · exact Or.inr ⟨hxF, fun h => hx ⟨hxj, h⟩⟩
          · rintro (rfl | ⟨hxF, hxB⟩)
            · exact ⟨hBF hj, fun h => h.1 rfl⟩
            · exact ⟨hxF, fun h => hxB h.2⟩
        have hjn : j ∉ F \ B := fun h => (Finset.mem_sdiff.1 h).2 hj
        rw [heq, Finset.sum_insert hjn, add_comm]
        exact hcon k
      have h2 := hmin hB' (Finset.erase_subset j B)
      exact Finset.notMem_erase j B (h2 hj)
    · rintro ⟨hBF, hfeas, hj⟩
      refine ⟨⟨hBF, (feasibleSet_iff_7bdd46e5 P _).2 hfeas⟩, ?_⟩
      rintro B' ⟨hB'F, hB'feas⟩ hB'B
      intro x hxB
      by_contra hxB'
      obtain ⟨k, hk⟩ := hj x hxB
      have hfe := (feasibleSet_iff_7bdd46e5 P _).1 hB'feas k
      have hsub : insert x (F \ B) ⊆ F \ B' := by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact Finset.mem_sdiff.2 ⟨hBF hxB, hxB'⟩
        · rw [Finset.mem_sdiff] at hy ⊢
          exact ⟨hy.1, fun h => hy.2 (hB'B h)⟩
      have hxn : x ∉ F \ B := fun h => (Finset.mem_sdiff.1 h).2 hxB
      have hmono := Finset.sum_le_sum_of_subset (f := fun i => P.r i k) hsub
      rw [Finset.sum_insert hxn] at hmono
      omega
