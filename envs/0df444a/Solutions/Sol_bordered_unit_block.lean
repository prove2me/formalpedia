-- Prove2me | solution 1 for bordered_unit_block
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:14.790385+00:00
-- url     : https://prove2.me/submissions/c0d08b7b-7cf9-44d7-83e1-26953d7aa6dc

import Theorems.Thm_adjugate_symm_fin_four
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

open Matrix in
theorem solution (H : Matrix (Fin 4) (Fin 4) ℝ) (g : Fin 4 → ℝ)
    (hS : H.transpose = H) (h22 : H 2 2 = 1) (h33 : H 3 3 = 1) (h23 : H 2 3 = 0) :
    g ⬝ᵥ H.adjugate.mulVec g =
      (g 2 ^ 2 + g 3 ^ 2) *
          ((H 0 0 - H 0 2 ^ 2 - H 0 3 ^ 2) * (H 1 1 - H 1 2 ^ 2 - H 1 3 ^ 2)
            - (H 0 1 - H 0 2 * H 1 2 - H 0 3 * H 1 3) ^ 2) +
        ((H 1 1 - H 1 2 ^ 2 - H 1 3 ^ 2) * (g 0 - H 0 2 * g 2 - H 0 3 * g 3) ^ 2
          - 2 * (H 0 1 - H 0 2 * H 1 2 - H 0 3 * H 1 3) *
              (g 0 - H 0 2 * g 2 - H 0 3 * g 3) * (g 1 - H 1 2 * g 2 - H 1 3 * g 3)
          + (H 0 0 - H 0 2 ^ 2 - H 0 3 ^ 2) * (g 1 - H 1 2 * g 2 - H 1 3 * g 3) ^ 2) := by
  have hs : ∀ i j, H j i = H i j := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hS i) j
  have hH : H = !![H 0 0, H 0 1, H 0 2, H 0 3;
      H 0 1, H 1 1, H 1 2, H 1 3;
      H 0 2, H 1 2, 1, 0;
      H 0 3, H 1 3, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h22, h33, h23] <;>
      first | exact hs _ _ | exact (hs _ _).trans h23
  rw [hH, adjugate_symm_fin_four]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  simp
  ring
