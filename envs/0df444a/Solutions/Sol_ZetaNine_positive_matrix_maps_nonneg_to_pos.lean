-- Prove2me | solution 1 for ZetaNine.positive_matrix_maps_nonneg_to_pos
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T03:26:13.987505+00:00
-- url     : https://prove2.me/submissions/8c4f1393-c53f-4805-b40f-0cadde48fe29

import Mathlib

theorem solution
    (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : ∀ i j : Fin 5, 0 < M i j)
    (v : Fin 5 → ℝ) (hv : v ≠ 0) (hvnn : ∀ i : Fin 5, 0 ≤ v i) :
    ∀ i : Fin 5, 0 < M.mulVec v i := by
  have hsome : ∃ j : Fin 5, 0 < v j := by
    by_contra h
    have hle : ∀ j : Fin 5, v j ≤ 0 := fun j => not_lt.mp fun hj => h ⟨j, hj⟩
    exact hv (funext fun j => le_antisymm (hle j) (hvnn j))
  obtain ⟨j₀, hj₀⟩ := hsome
  intro i
  rw [Matrix.mulVec_apply]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (le_of_lt (hM i j)) (hvnn j))
    ⟨j₀, Finset.mem_univ j₀, mul_pos (hM i j₀) hj₀⟩
