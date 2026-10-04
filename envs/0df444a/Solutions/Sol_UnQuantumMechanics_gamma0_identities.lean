-- Prove2me | solution 1 for UnQuantumMechanics.gamma0_identities
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:03:45.574979+00:00
-- url     : https://prove2.me/submissions/d4888e5f-b8a2-44cf-b657-8cab26fc9432

import Mathlib
import Definitions.Def_UnQM_phase_space

set_option autoImplicit false

open Matrix

namespace UnQuantumMechanics.G0Aux

theorem eta0_transpose : eta0ᵀ = -eta0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0]

theorem eta0_mul_self : eta0 * eta0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0, Matrix.mul_apply, Fin.sum_univ_two]

theorem one_kron_neg (n : ℕ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin n) (Fin n) ℝ) (-B)
      = -Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin n) (Fin n) ℝ) B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.kroneckerMap_apply]

theorem gamma0_transpose (n : ℕ) : (gamma0 n)ᵀ = -gamma0 n := by
  unfold gamma0
  rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_one, eta0_transpose, one_kron_neg]

theorem gamma0_mul_self (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  unfold gamma0
  have h := (Matrix.mul_kronecker_mul (1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) eta0 eta0).symm
  rw [h, Matrix.mul_one, eta0_mul_self, one_kron_neg]
  rw [show Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin n) (Fin n) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 from Matrix.one_kronecker_one]

end UnQuantumMechanics.G0Aux

open Matrix UnQuantumMechanics in
theorem solution (n : ℕ) :
    (gamma0 n)ᵀ = -gamma0 n ∧ gamma0 n * gamma0 n = -1 ∧ (gamma0 n)ᵀ * gamma0 n = 1 := by
  refine ⟨UnQuantumMechanics.G0Aux.gamma0_transpose n,
    UnQuantumMechanics.G0Aux.gamma0_mul_self n, ?_⟩
  rw [UnQuantumMechanics.G0Aux.gamma0_transpose, Matrix.neg_mul,
    UnQuantumMechanics.G0Aux.gamma0_mul_self, neg_neg]
