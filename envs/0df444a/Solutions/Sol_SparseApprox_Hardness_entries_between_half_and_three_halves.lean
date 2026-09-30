-- Prove2me | solution 1 for SparseApprox.Hardness.entries_between_half_and_three_halves
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T04:57:08.765257+00:00
-- url     : https://prove2.me/submissions/6191cdea-8602-4469-9a41-e5fb79ab500b

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

open SparseApprox.Hardness

theorem solution {m n : ℕ} (C : Fin n → Finset (Fin m))
    (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖Matrix.toEuclideanLin (incidence C) x - onesVec m‖ ≤ 1 / 2) (i : Fin m) :
    1 / 2 ≤ (Matrix.toEuclideanLin (incidence C) x) i ∧
      (Matrix.toEuclideanLin (incidence C) x) i ≤ 3 / 2 := by
  have hcoord : ‖(Matrix.toEuclideanLin (incidence C) x - onesVec m) i‖ ≤ 1 / 2 :=
    (PiLp.norm_apply_le _ i).trans hx
  have hone : (onesVec m) i = 1 := rfl
  rw [PiLp.sub_apply, hone, Real.norm_eq_abs] at hcoord
  constructor <;> linarith [abs_le.mp hcoord]
