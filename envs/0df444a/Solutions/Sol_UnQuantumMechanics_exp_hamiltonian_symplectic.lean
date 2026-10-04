-- Prove2me | solution 1 for UnQuantumMechanics.exp_hamiltonian_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:56:53.260765+00:00
-- url     : https://prove2.me/submissions/f56a030d-e553-43c6-b1b5-521a227e7450

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

namespace F0710a32Aux

open UnQuantumMechanics

lemma eta0_mul_self : eta0 * eta0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0, Matrix.mul_apply, Fin.sum_univ_two]

lemma eta0_transpose : eta0ᵀ = -eta0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0]

lemma gamma0_mul_self (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  unfold gamma0
  rw [← Matrix.mul_kronecker_mul, eta0_mul_self, Matrix.mul_one]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : i = j <;> by_cases h2 : a = b <;> simp [h1, h2]

lemma gamma0_transpose (n : ℕ) : (gamma0 n)ᵀ = -gamma0 n := by
  unfold gamma0
  ext ⟨i, a⟩ ⟨j, b⟩
  have h := congrFun (congrFun eta0_transpose a) b
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  simp only [Matrix.transpose_apply, Matrix.kroneckerMap_apply, Matrix.neg_apply, h]
  by_cases h1 : i = j
  · subst h1; simp
  · simp [h1, Ne.symm h1]

end F0710a32Aux

open UnQuantumMechanics in
theorem solution (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H) (τ : ℝ) :
    IsSymplecticMatrix n (NormedSpace.exp (τ • H)) := by
  obtain ⟨A, hA, rfl⟩ := hH
  set g := gamma0 n with hg
  have hgg : g * g = -1 := F0710a32Aux.gamma0_mul_self n
  have hgt : gᵀ = -g := F0710a32Aux.gamma0_transpose n
  have hinv : g⁻¹ = -g := by
    rw [Matrix.inv_eq_right_inv]
    rw [Matrix.mul_neg, hgg, neg_neg]
  have hunit : IsUnit g := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have : g * (-g) = 1 := by rw [Matrix.mul_neg, hgg, neg_neg]
    exact (Matrix.isUnit_det_of_right_inverse this)
  have hAt : Aᵀ = A := hA
  -- H^T = A^T g^T = -A g
  have hHt : (g * A)ᵀ = -(A * g) := by
    rw [Matrix.transpose_mul, hAt, hgt, Matrix.mul_neg]
  have hconj : g * (-(τ • (g * A)ᵀ)) * g⁻¹ = τ • (g * A) := by
    rw [hHt, hinv, smul_neg, neg_neg, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc g (A * g) g, Matrix.mul_assoc A g g, hgg]
    simp
  have hexp : NormedSpace.exp (τ • (g * A)) =
      g * NormedSpace.exp (-(τ • (g * A)ᵀ)) * g⁻¹ := by
    rw [← hconj, Matrix.exp_conj _ _ hunit]
  unfold IsSymplecticMatrix
  rw [← hg]
  have htr : (NormedSpace.exp (τ • (g * A)))ᵀ = NormedSpace.exp (τ • (g * A)ᵀ) := by
    rw [← Matrix.exp_transpose, Matrix.transpose_smul]
  rw [htr]
  conv_lhs => rw [hexp]
  have hcomm : Commute (-(τ • (g * A)ᵀ)) (τ • (g * A)ᵀ) := (Commute.refl _).neg_left
  rw [Matrix.mul_assoc (g * NormedSpace.exp (-(τ • (g * A)ᵀ))) g⁻¹ g,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit), Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]
