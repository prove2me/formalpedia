-- Prove2me | solution 1 for SmaleNinth.div_row_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T08:06:35.54902+00:00
-- url     : https://prove2.me/submissions/e5e7c7c0-c863-402d-a936-673fb8eb1c8e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

open Matrix

theorem solution {n : ℕ}
    (u z : Fin n → ℝ) (d : ℝ) :
    ((fun k => u k / d) ⬝ᵥ z) = (u ⬝ᵥ z) / d := by
  calc
    ((fun k => u k / d) ⬝ᵥ z) =
        ∑ k, (u k * z k) / d := by
          rw [dotProduct]
          apply Finset.sum_congr rfl
          intro k hk
          rw [div_eq_mul_inv]
          ring
    _ = (∑ k, u k * z k) / d :=
      (Finset.sum_div (Finset.univ : Finset (Fin n))
        (fun k : Fin n => u k * z k) d).symm
    _ = (u ⬝ᵥ z) / d := by
      rw [dotProduct]
