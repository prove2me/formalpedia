-- Prove2me | solution 1 for ZeroOneExpansion.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:56:48.799527+00:00
-- url     : https://prove2.me/submissions/29046982-bd4f-45bb-b6b2-3477ed77f555

import Mathlib
import Definitions.Def_ZeroOneExpansion_compatR

set_option autoImplicit false

open Matrix

open ZeroOneExpansion in
theorem solution (c₀ d₀ : Fin 2 → ℝ) (hc : c₀ ∈ C) (hd : d₀ ∈ D) :
    (∃ w : Fin 2 → ℝ, (∀ x ∈ C, x ≠ c₀ → w ⬝ᵥ x < w ⬝ᵥ c₀) ∧
        (∀ x ∈ D, x ≠ d₀ → w ⬝ᵥ x < w ⬝ᵥ d₀)) ↔
      (c₀, d₀) ∈ compatR := by
  simp only [C, D, Set.mem_insert_iff, Set.mem_singleton_iff] at hc hd
  constructor
  · rintro ⟨w, h1, h2⟩
    have k1 := h1 ![0, 0] (by simp [C])
    have k2 := h1 ![0, 1] (by simp [C])
    have k3 := h1 ![1, 0] (by simp [C])
    have k4 := h1 ![1, 1] (by simp [C])
    have l1 := h2 ![0, 0] (by simp [D])
    have l2 := h2 ![1, 0] (by simp [D])
    have l3 := h2 ![0, 1] (by simp [D])
    rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
      simp [compatR, dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at k1 k2 k3 k4 l1 l2 l3 ⊢ <;>
      linarith
  · intro h
    rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
      simp [compatR, Matrix.vecCons_inj] at h
    · refine ⟨![-1, -1], fun x hx hne => ?_, fun x hx hne => ?_⟩
      · simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
      · simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
    · refine ⟨![-1, 1], fun x hx hne => ?_, fun x hx hne => ?_⟩
      · simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
      · simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
    · refine ⟨![1, -1], fun x hx hne => ?_, fun x hx hne => ?_⟩
      · simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
      · simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
    · refine ⟨![2, 1], fun x hx hne => ?_, fun x hx hne => ?_⟩
      · simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
      · simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
    · refine ⟨![1, 2], fun x hx hne => ?_, fun x hx hne => ?_⟩
      · simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
      · simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl <;>
          simp [dotProduct, Fin.sum_univ_two, Matrix.vecCons_inj] at hne ⊢ <;> norm_num
