-- Prove2me | solution 1 for categorical_covariance_sandwich_shift_invariant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T04:35:25.455771+00:00
-- url     : https://prove2.me/submissions/ae475fb7-888a-4000-b0a5-c8b1562b024b

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators

set_option autoImplicit false

/-- The categorical covariance sandwich is invariant under a common translation
of every feature column. Only normalization of the weights is needed for this
algebraic identity; nonnegativity is needed for a probabilistic interpretation. -/
theorem solution {m n : Type*} [Fintype n] [DecidableEq n]
    (p : n → ℝ) (hp : ∑ j, p j = 1) (X : Matrix m n ℝ) (c : m → ℝ) :
    (X - Matrix.vecMulVec c (fun _ : n => (1 : ℝ))) *
        (Matrix.diagonal p - Matrix.vecMulVec p p) *
        (X - Matrix.vecMulVec c (fun _ : n => (1 : ℝ))).transpose =
      X * (Matrix.diagonal p - Matrix.vecMulVec p p) * X.transpose := by
  let C : Matrix n n ℝ := Matrix.diagonal p - Matrix.vecMulVec p p
  let D : Matrix m n ℝ := Matrix.vecMulVec c (fun _ : n => (1 : ℝ))
  have hrow (i : n) : ∑ j, C i j = 0 := by
    simp [C, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
  have hcol (j : n) : ∑ i, C i j = 0 := by
    simp [C, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hp]
  have hDC : D * C = 0 := by
    ext i j
    simp [D, Matrix.mul_apply, Matrix.vecMulVec_apply, ← Finset.mul_sum, hcol]
  have hCD : C * D.transpose = 0 := by
    rw [show D.transpose = Matrix.vecMulVec (fun _ : n => (1 : ℝ)) c by
      exact Matrix.transpose_vecMulVec _ _]
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, ← Finset.sum_mul, hrow]
  change (X - D) * C * (X - D).transpose = X * C * X.transpose
  rw [Matrix.sub_mul, hDC, sub_zero, Matrix.transpose_sub, Matrix.mul_sub,
    Matrix.mul_assoc X C D.transpose, hCD, Matrix.mul_zero, sub_zero]
