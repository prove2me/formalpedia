-- Prove2me | solution 1 for UnQuantumMechanics.skew_symm_eigenvalue_neg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:50:29.591394+00:00
-- url     : https://prove2.me/submissions/7b4781b4-8073-4f06-b9f2-cd3ecb1162cf

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

theorem skewNegEig_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hAt : Aᵀ = -A) (μ : ℂ)
    (hμ : (scalar (Fin n) μ - A).det = 0) : (scalar (Fin n) (-μ) - A).det = 0 := by
  have h1 : scalar (Fin n) (-μ) - A = -(scalar (Fin n) μ - A)ᵀ := by
    rw [Matrix.transpose_sub, hAt, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_transpose, ← Matrix.diagonal_neg]
    abel
  rw [h1, Matrix.det_neg, Matrix.det_transpose, hμ, mul_zero]

open Matrix in
theorem solution {ν : ℕ} (J : Matrix (Fin ν) (Fin ν) ℝ) (hJ : Jᵀ = -J)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (Matrix.toLin' (J.map (algebraMap ℝ ℂ))) μ) :
    Module.End.HasEigenvalue (Matrix.toLin' (J.map (algebraMap ℝ ℂ))) (-μ) := by
  have hAt : (J.map (algebraMap ℝ ℂ))ᵀ = -(J.map (algebraMap ℝ ℂ)) := by
    rw [← Matrix.transpose_map, hJ]
    ext i j
    simp
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    Polynomial.IsRoot.def, Matrix.eval_charpoly] at hμ ⊢
  exact skewNegEig_aux _ hAt μ hμ
