-- Prove2me | solution 1 for PfisterCEP.allOnes_eigensystem
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-05T02:04:51.593676+00:00
-- url     : https://prove2.me/submissions/e327cf67-4341-4696-9dcd-d9de7062f354

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

theorem solution (N : ℕ) :
    Matrix.mulVec (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin N) (Fin N) ℝ)
        (fun _ => 1) = (N : ℝ) • (fun _ => (1 : ℝ)) ∧
    (∀ k l : Fin N, Matrix.mulVec
      (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin N) (Fin N) ℝ)
      (Pi.single k 1 - Pi.single l 1) = 0) ∧
    (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin N) (Fin N) ℝ).charpoly =
      Polynomial.X ^ N - Polynomial.C (N : ℝ) * Polynomial.X ^ (N - 1) := by
  constructor
  · ext i
    simp [Matrix.mulVec, dotProduct]
  constructor
  · intro k l
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib]
  · have hJ : (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin N) (Fin N) ℝ) =
        Matrix.vecMulVec (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) := by
      ext i j
      simp [Matrix.vecMulVec]
    rw [hJ, Matrix.charpoly_vecMulVec]
    simp [dotProduct, Polynomial.smul_eq_C_mul]
