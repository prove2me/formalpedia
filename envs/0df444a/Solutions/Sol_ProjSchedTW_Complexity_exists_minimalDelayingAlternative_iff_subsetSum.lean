-- Prove2me | solution 1 for ProjSchedTW.Complexity.exists_minimalDelayingAlternative_iff_subsetSum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:08:59.662986+00:00
-- url     : https://prove2.me/submissions/d0aaee10-d69a-4f76-a332-828312227b57

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives

set_option autoImplicit false

open ProjSchedTW.Complexity in
lemma b6013b02_feas_iff {n : ℕ} (r : Fin (n + 2) → Fin 1 → ℕ) (R : Fin 1 → ℕ)
    (X : Finset (Fin (n + 2))) :
    IsFeasibleSet r R X ↔ ∑ i ∈ X, r i 0 ≤ R 0 := by
  unfold IsFeasibleSet IsForbiddenSet
  constructor
  · intro h
    by_contra h'
    exact h ⟨0, by omega⟩
  · rintro h ⟨k, hk⟩
    have : k = 0 := Subsingleton.elim _ _
    subst this
    omega

open ProjSchedTW.Complexity in
theorem solution {n : ℕ} (r : Fin (n + 2) → Fin 1 → ℕ)
    (R : Fin 1 → ℕ) (F : Finset (Fin (n + 2))) (jstar : Fin (n + 2)) (hjF : jstar ∈ F)
    (hr : r jstar 0 = 1) :
    (∃ B, IsMinimalDelayingAlternative r R F B ∧ jstar ∈ B) ↔
      ∃ A ⊆ F.erase jstar, ∑ i ∈ A, r i 0 = R 0 := by
  constructor
  · rintro ⟨B, ⟨⟨hBF, hfeas⟩, hmin⟩, hj⟩
    refine ⟨F \ B, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_erase]
      exact ⟨fun h => hx.2 (h ▸ hj), hx.1⟩
    · have h1 := (b6013b02_feas_iff r R _).1 hfeas
      have h2 := hmin (B.erase jstar) (Finset.erase_ssubset hj)
      have hsub : (B.erase jstar) ⊆ F := (Finset.erase_subset _ _).trans hBF
      have h3 : ¬ (∑ i ∈ F \ B.erase jstar, r i 0 ≤ R 0) := by
        intro h
        exact h2 ⟨hsub, (b6013b02_feas_iff r R _).2 h⟩
      have heq : F \ B.erase jstar = insert jstar (F \ B) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hx2⟩
          by_cases hxj : x = jstar
          · exact Or.inl hxj
          · exact Or.inr ⟨hx, fun hb => hx2 ⟨hxj, hb⟩⟩
        · rintro (hx | ⟨hx, hx2⟩)
          · subst hx; exact ⟨hjF, fun h => h.1 rfl⟩
          · exact ⟨hx, fun h => hx2 h.2⟩
      have hnot : jstar ∉ F \ B := by
        rw [Finset.mem_sdiff]; exact fun h => h.2 hj
      rw [heq, Finset.sum_insert hnot, hr] at h3
      omega
  · rintro ⟨A, hA, hsum⟩
    classical
    set Z := F.filter (fun i => r i 0 = 0) with hZ
    set A' := A ∪ Z with hA'
    have hAF : A ⊆ F := hA.trans (Finset.erase_subset _ _)
    have hA'F : A' ⊆ F := Finset.union_subset hAF (Finset.filter_subset _ _)
    have hZsum : ∑ i ∈ Z, r i 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hZ, Finset.mem_filter] at hi
      exact hi.2
    have hS : ∑ i ∈ A', r i 0 = R 0 := by
      have h1 := Finset.sum_union_inter (s₁ := A) (s₂ := Z) (f := fun i => r i 0)
      have h2 : ∑ i ∈ A, r i 0 ≤ ∑ i ∈ A', r i 0 :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
      rw [← hA'] at h1
      omega
    have hjA' : jstar ∉ A' := by
      rw [hA', Finset.mem_union, not_or]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := hA h
        simp at this
      · rw [hZ, Finset.mem_filter] at h
        omega
    refine ⟨F \ A', ⟨⟨Finset.sdiff_subset, ?_⟩, ?_⟩, ?_⟩
    · rw [Finset.sdiff_sdiff_eq_self hA'F, b6013b02_feas_iff]
      omega
    · rintro B' hB' ⟨hB'F, hfeas'⟩
      obtain ⟨b, hbB, hbB'⟩ := Finset.exists_of_ssubset hB'
      rw [Finset.mem_sdiff] at hbB
      have hrb : r b 0 ≠ 0 := by
        intro h0
        apply hbB.2
        rw [hA', Finset.mem_union]
        right
        rw [hZ, Finset.mem_filter]
        exact ⟨hbB.1, h0⟩
      have hsubset : insert b A' ⊆ F \ B' := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rw [Finset.mem_sdiff]
        rcases hx with hx | hx
        · subst hx; exact ⟨hbB.1, hbB'⟩
        · refine ⟨hA'F hx, fun hxB' => ?_⟩
          have := hB'.1 hxB'
          rw [Finset.mem_sdiff] at this
          exact this.2 hx
      have hle := Finset.sum_le_sum_of_subset (f := fun i => r i 0) hsubset
      rw [Finset.sum_insert hbB.2] at hle
      have := (b6013b02_feas_iff r R _).1 hfeas'
      omega
    · rw [Finset.mem_sdiff]; exact ⟨hjF, hjA'⟩
