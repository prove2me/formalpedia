-- Prove2me | solution 1 for SparseApprox.Greedy.residual_sq_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T23:14:18.04989+00:00
-- url     : https://prove2.me/submissions/11f74e37-119d-4013-9d27-818bcc78db3d

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one

open scoped InnerProductSpace
open SparseApprox.Greedy

private lemma selected_norm_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r < t) :
    ‖(greedyState A b k r).col (k r)‖ = 1 := by
  rcases state_col_norm_zero_or_one A b k r (k r) with hzero | hone
  · exfalso
    exact (hrun r hr).2.2.1 (by simp [hzero])
  · exact hone

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r < t) :
    ‖(greedyState A b k (r + 1)).res‖ ^ 2 =
      ‖(greedyState A b k r).res‖ ^ 2 -
        |⟪(greedyState A b k r).col (k r),
          (greedyState A b k r).res⟫_ℝ| ^ 2 := by
  have hknorm :
      ‖(greedyState A b k r).col (k r)‖ = 1 :=
    selected_norm_one A b ε k t r hrun hr
  rw [show
    (greedyState A b k (r + 1)).res =
      (greedyState A b k r).res -
        ⟪(greedyState A b k r).col (k r),
          (greedyState A b k r).res⟫_ℝ •
          (greedyState A b k r).col (k r) by
      simp [greedyState, greedyStep]]
  rw [norm_sub_sq_real, real_inner_smul_right]
  rw [real_inner_comm]
  rw [norm_smul, Real.norm_eq_abs, hknorm, mul_one, sq_abs]
  ring
