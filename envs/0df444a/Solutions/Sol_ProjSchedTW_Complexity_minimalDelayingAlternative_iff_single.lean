-- Prove2me | solution 1 for ProjSchedTW.Complexity.minimalDelayingAlternative_iff_single
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:54:31.053038+00:00
-- url     : https://prove2.me/submissions/f796f30c-b212-40ab-a2ab-831c596f9893

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives

set_option autoImplicit false

open ProjSchedTW.Complexity in
theorem P405e877a_feasible_iff {n : ℕ} (r : Fin (n + 2) → Fin 1 → ℕ) (R : Fin 1 → ℕ)
    (A : Finset (Fin (n + 2))) :
    IsFeasibleSet r R A ↔ ∑ i ∈ A, (r i 0 : ℤ) ≤ (R 0 : ℤ) := by
  unfold IsFeasibleSet IsForbiddenSet
  push_cast
  constructor
  · intro h
    push_neg at h
    have := h 0
    exact_mod_cast this
  · intro h ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim _ _
    subst hk0
    have : ∑ i ∈ A, (r i 0 : ℤ) = ((∑ i ∈ A, r i 0 : ℕ) : ℤ) := by push_cast; rfl
    omega

open ProjSchedTW.Complexity in
theorem solution {n : ℕ} (r : Fin (n + 2) → Fin 1 → ℕ)
    (R : Fin 1 → ℕ) (F B : Finset (Fin (n + 2))) (jstar : Fin (n + 2)) (hBF : B ⊆ F)
    (hj : jstar ∈ B) :
    IsMinimalDelayingAlternative r R F B ↔
      ((R 0 : ℤ) - B.inf' ⟨jstar, hj⟩ (fun j => (r j 0 : ℤ)) < ∑ i ∈ F \ B, (r i 0 : ℤ) ∧
        ∑ i ∈ F \ B, (r i 0 : ℤ) ≤ (R 0 : ℤ)) := by
  unfold IsMinimalDelayingAlternative IsDelayingAlternative
  simp only [P405e877a_feasible_iff]
  -- key: for j ∈ B, ∑ over F \ (B.erase j) = ∑ over F \ B + r j
  have key : ∀ j ∈ B, ∑ i ∈ F \ B.erase j, (r i 0 : ℤ) = ∑ i ∈ F \ B, (r i 0 : ℤ) + r j 0 := by
    intro j hjB
    have hjF : j ∈ F := hBF hjB
    have hset : F \ B.erase j = insert j (F \ B) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hxF, hx⟩
        by_cases hxj : x = j
        · exact Or.inl hxj
        · exact Or.inr ⟨hxF, fun hxB => hx ⟨hxj, hxB⟩⟩
      · rintro (rfl | ⟨hxF, hxB⟩)
        · exact ⟨hjF, fun h => h.1 rfl⟩
        · exact ⟨hxF, fun h => hxB h.2⟩
    have hjn : j ∉ F \ B := fun h => (Finset.mem_sdiff.1 h).2 hjB
    rw [hset, Finset.sum_insert hjn, add_comm]
  constructor
  · rintro ⟨⟨-, hfeas⟩, hmin⟩
    refine ⟨?_, hfeas⟩
    obtain ⟨j, hjB, hjeq⟩ := Finset.exists_mem_eq_inf' ⟨jstar, hj⟩ (fun j => (r j 0 : ℤ))
    rw [hjeq]
    have h1 := hmin (B.erase j) (Finset.erase_ssubset hjB)
    have h2 : ¬ (∑ i ∈ F \ B.erase j, (r i 0 : ℤ) ≤ (R 0 : ℤ)) := by
      intro h
      exact h1 ⟨(Finset.erase_subset j B).trans hBF, h⟩
    rw [key j hjB] at h2
    linarith
  · rintro ⟨hlt, hle⟩
    refine ⟨⟨hBF, hle⟩, ?_⟩
    rintro B' hB' ⟨-, hfeas'⟩
    obtain ⟨j, hjB, hjB'⟩ := Finset.exists_of_ssubset hB'
    have hsub : F \ B.erase j ⊆ F \ B' := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_erase] at hx ⊢
      refine ⟨hx.1, fun hxB' => hx.2 ⟨?_, hB'.1 hxB'⟩⟩
      rintro rfl
      exact hjB' hxB'
    have hmono : ∑ i ∈ F \ B.erase j, (r i 0 : ℤ) ≤ ∑ i ∈ F \ B', (r i 0 : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    rw [key j hjB] at hmono
    have hinf : B.inf' ⟨jstar, hj⟩ (fun j => (r j 0 : ℤ)) ≤ (r j 0 : ℤ) :=
      Finset.inf'_le _ hjB
    linarith
