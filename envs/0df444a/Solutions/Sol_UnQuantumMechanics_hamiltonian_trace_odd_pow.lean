-- Prove2me | solution 1 for UnQuantumMechanics.hamiltonian_trace_odd_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:02:36.01498+00:00
-- url     : https://prove2.me/submissions/13689801-2f1f-4ab9-af3c-166863dd061f

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

open UnQuantumMechanics in
lemma p98f_gamma0_transpose (n : ℕ) : (gamma0 n)ᵀ = -gamma0 n := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [gamma0, transpose_apply, kroneckerMap_apply, eta0, one_apply]
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;> simp [h, eq_comm]

open UnQuantumMechanics in
theorem solution (n : ℕ) (S : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hS : IsHamiltonianMatrix n S) (k : ℕ) :
    (S ^ (2 * k + 1)).trace = 0 := by
  obtain ⟨A, hA, rfl⟩ := hS
  set g := gamma0 n with hg
  have hgT : gᵀ = -g := p98f_gamma0_transpose n
  have hAT : Aᵀ = A := hA
  have hsc : ∀ m : ℕ, g * (A * g) ^ m = (g * A) ^ m * g := by
    intro m
    have : SemiconjBy g (A * g) (g * A) := by
      unfold SemiconjBy; simp [Matrix.mul_assoc]
    exact (this.pow_right m).eq
  have hcyc : ∀ m : ℕ, ((g * A) ^ m).trace = ((A * g) ^ m).trace := by
    intro m
    cases m with
    | zero => simp
    | succ m =>
      rw [pow_succ, pow_succ', ← Matrix.mul_assoc, ← hsc m, Matrix.mul_assoc,
        Matrix.trace_mul_comm, Matrix.mul_assoc, (pow_succ (A * g) m).symm,
        (pow_succ' (A * g) m).symm]
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  have h : ((g * A) ^ (2 * k + 1)).trace = -((g * A) ^ (2 * k + 1)).trace := by
    calc ((g * A) ^ (2 * k + 1)).trace = (((g * A) ^ (2 * k + 1))ᵀ).trace :=
          (Matrix.trace_transpose _).symm
      _ = (((g * A)ᵀ) ^ (2 * k + 1)).trace := by rw [Matrix.transpose_pow]
      _ = ((-(A * g)) ^ (2 * k + 1)).trace := by
          rw [Matrix.transpose_mul, hgT, hAT, Matrix.mul_neg]
      _ = -((A * g) ^ (2 * k + 1)).trace := by
          rw [hodd.neg_pow, Matrix.trace_neg]
      _ = -((g * A) ^ (2 * k + 1)).trace := by rw [hcyc]
  linarith
