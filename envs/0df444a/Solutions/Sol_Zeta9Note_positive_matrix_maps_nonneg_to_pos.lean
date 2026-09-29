-- Prove2me | solution 1 for Zeta9Note.positive_matrix_maps_nonneg_to_pos
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T08:23:22.316251+00:00
-- url     : https://prove2.me/submissions/e475cc2e-3937-44c1-9992-c63984d86d05

-- Public-mission submission for Zeta9Note.positive_matrix_maps_nonneg_to_pos.
-- Statement and proof verified in formalization/Zeta9Note.lean (exit 0, no placeholder).

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
