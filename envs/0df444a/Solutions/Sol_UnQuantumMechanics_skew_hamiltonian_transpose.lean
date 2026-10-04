-- Prove2me | solution 1 for UnQuantumMechanics.skew_hamiltonian_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:22:10.480731+00:00
-- url     : https://prove2.me/submissions/64aedc0f-97cf-4366-b37b-e2bd2799c3af

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

lemma p5f9f2d8b_eta0_sq : eta0 * eta0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0, Matrix.mul_apply, Fin.sum_univ_two]

lemma p5f9f2d8b_eta0_tr : eta0ᵀ = -eta0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0]

lemma p5f9f2d8b_gamma0_eq (n : ℕ) : gamma0 n = Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin n) (Fin n) ℝ) eta0 := rfl

lemma p5f9f2d8b_kron_neg (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.kroneckerMap (· * ·) A (-B) = -Matrix.kroneckerMap (· * ·) A B := by
  ext i j
  simp [Matrix.kroneckerMap_apply]

lemma p5f9f2d8b_gamma0_sq (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  rw [p5f9f2d8b_gamma0_eq, ← Matrix.mul_kronecker_mul, Matrix.one_mul, p5f9f2d8b_eta0_sq,
    p5f9f2d8b_kron_neg, Matrix.one_kronecker_one]

lemma p5f9f2d8b_gamma0_tr (n : ℕ) : (gamma0 n)ᵀ = -gamma0 n := by
  rw [p5f9f2d8b_gamma0_eq, ← Matrix.kroneckerMap_transpose, Matrix.transpose_one,
    p5f9f2d8b_eta0_tr, p5f9f2d8b_kron_neg]

end UnQuantumMechanics

open Matrix UnQuantumMechanics in
theorem solution (n : ℕ) (C : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hC : IsSkewHamiltonianMatrix n C) :
    Cᵀ = -(gamma0 n * C * gamma0 n) := by
  obtain ⟨B, hB, rfl⟩ := hC
  rw [Matrix.transpose_mul, hB, p5f9f2d8b_gamma0_tr, ← Matrix.mul_assoc,
    p5f9f2d8b_gamma0_sq]
  simp
