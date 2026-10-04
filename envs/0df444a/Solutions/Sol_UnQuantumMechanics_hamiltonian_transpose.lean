-- Prove2me | solution 1 for UnQuantumMechanics.hamiltonian_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:45:32.815948+00:00
-- url     : https://prove2.me/submissions/e6bd02c1-afdb-46aa-a1b8-77c02dd10360

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace UnQuantumMechanics

lemma p38fa7274_eta0_sq : eta0 * eta0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0, Matrix.mul_apply, Fin.sum_univ_two]

lemma p38fa7274_eta0_tr : eta0ᵀ = -eta0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0]

lemma p38fa7274_gamma0_eq (n : ℕ) : gamma0 n = Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin n) (Fin n) ℝ) eta0 := rfl

lemma p38fa7274_gamma0_sq (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  rw [p38fa7274_gamma0_eq, ← Matrix.mul_kronecker_mul, Matrix.one_mul, p38fa7274_eta0_sq,
    show (-1 : Matrix (Fin 2) (Fin 2) ℝ) = (-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) by simp,
    Matrix.kronecker_smul, Matrix.one_kronecker_one, neg_one_smul]

lemma p38fa7274_gamma0_tr (n : ℕ) : (gamma0 n)ᵀ = -gamma0 n := by
  rw [p38fa7274_gamma0_eq, ← Matrix.kroneckerMap_transpose, Matrix.transpose_one,
    p38fa7274_eta0_tr,
    show (-eta0 : Matrix (Fin 2) (Fin 2) ℝ) = (-1 : ℝ) • eta0 by simp,
    Matrix.kronecker_smul, neg_one_smul]

end UnQuantumMechanics

open Matrix UnQuantumMechanics in
theorem solution (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H) :
    Hᵀ = gamma0 n * H * gamma0 n := by
  obtain ⟨A, hA, rfl⟩ := hH
  rw [Matrix.transpose_mul, hA.eq, p38fa7274_gamma0_tr, ← Matrix.mul_assoc,
    p38fa7274_gamma0_sq]
  simp
