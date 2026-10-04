-- Prove2me | solution 1 for UnQuantumMechanics.hamiltonian_skew_hamiltonian_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:04:27.489925+00:00
-- url     : https://prove2.me/submissions/33b55846-eb9a-4ea0-9bb5-0d4ed02011af

import Mathlib
import Definitions.Def_UnQM_phase_space

set_option autoImplicit false

open Matrix

namespace UnQuantumMechanics

namespace AdcHSH

lemma gamma0_transpose (n : ℕ) : (gamma0 n)ᵀ = -gamma0 n := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [gamma0, eta0, kroneckerMap_apply, one_apply, eq_comm]

lemma gamma0_mul_self (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [gamma0, eta0, Matrix.mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two] <;> split_ifs <;> simp

/-- symplectic adjoint -/
noncomputable def sig (n : ℕ) (M : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) :
    Matrix (PhaseIdx n) (PhaseIdx n) ℝ :=
  -(gamma0 n * Mᵀ * gamma0 n)

lemma sig_mul (n : ℕ) (X Y : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) :
    sig n (X * Y) = sig n Y * sig n X := by
  have h := gamma0_mul_self n
  simp only [sig, transpose_mul, neg_mul_neg]
  calc -(gamma0 n * (Yᵀ * Xᵀ) * gamma0 n)
      = gamma0 n * Yᵀ * (-1 : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) * Xᵀ * gamma0 n := by
        simp [Matrix.mul_assoc]
    _ = gamma0 n * Yᵀ * gamma0 n * (gamma0 n * Xᵀ * gamma0 n) := by
        rw [← h]; simp [Matrix.mul_assoc]

lemma sig_add (n : ℕ) (X Y : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) :
    sig n (X + Y) = sig n X + sig n Y := by
  simp only [sig, transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

lemma sig_sub (n : ℕ) (X Y : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) :
    sig n (X - Y) = sig n X - sig n Y := by
  simp only [sig, transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma sig_one (n : ℕ) : sig n 1 = 1 := by
  simp [sig, gamma0_mul_self]

lemma sig_pow (n : ℕ) (X : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (k : ℕ) :
    sig n (X ^ k) = sig n X ^ k := by
  induction k with
  | zero => simp [sig_one]
  | succ k ih => rw [pow_succ', sig_mul, ih, ← pow_succ]

lemma ham_iff (n : ℕ) (M : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) :
    IsHamiltonianMatrix n M ↔ sig n M = -M := by
  have h := gamma0_mul_self n
  have ht := gamma0_transpose n
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hA' : Aᵀ = A := hA
    simp only [sig, transpose_mul, hA', ht]
    calc -(gamma0 n * (A * -gamma0 n) * gamma0 n)
        = gamma0 n * A * (gamma0 n * gamma0 n) := by simp [Matrix.mul_assoc]
      _ = -(gamma0 n * A) := by rw [h]; simp
  · intro hM
    refine ⟨-(gamma0 n * M), ?_, ?_⟩
    · -- (G M)ᵀ = Mᵀ Gᵀ = -Mᵀ G ; need = G M
      have e : gamma0 n * Mᵀ * gamma0 n = M := by
        have := congrArg Neg.neg hM; simpa [sig] using this
      have e2 : Mᵀ * gamma0 n = -(gamma0 n * M) := by
        calc Mᵀ * gamma0 n = -(gamma0 n * gamma0 n) * (Mᵀ * gamma0 n) := by rw [h]; simp
          _ = -(gamma0 n * (gamma0 n * Mᵀ * gamma0 n)) := by simp [Matrix.mul_assoc]
          _ = -(gamma0 n * M) := by rw [e]
      show (-(gamma0 n * M))ᵀ = -(gamma0 n * M)
      rw [transpose_neg, transpose_mul, ht, Matrix.mul_neg, neg_neg, e2]
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, h]; simp

lemma skew_iff (n : ℕ) (M : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) :
    IsSkewHamiltonianMatrix n M ↔ sig n M = M := by
  have h := gamma0_mul_self n
  have ht := gamma0_transpose n
  constructor
  · rintro ⟨B, hB, rfl⟩
    simp only [sig, transpose_mul, hB, ht]
    calc -(gamma0 n * (-B * -gamma0 n) * gamma0 n)
        = -(gamma0 n * B * (gamma0 n * gamma0 n)) := by simp [Matrix.mul_assoc]
      _ = gamma0 n * B := by rw [h]; simp
  · intro hM
    refine ⟨-(gamma0 n * M), ?_, ?_⟩
    · have e : gamma0 n * Mᵀ * gamma0 n = -M := by
        rw [← neg_neg (gamma0 n * Mᵀ * gamma0 n)]; exact congrArg Neg.neg hM
      have e2 : Mᵀ * gamma0 n = gamma0 n * M := by
        calc Mᵀ * gamma0 n = -(gamma0 n * gamma0 n) * (Mᵀ * gamma0 n) := by rw [h]; simp
          _ = -(gamma0 n * (gamma0 n * Mᵀ * gamma0 n)) := by simp [Matrix.mul_assoc]
          _ = gamma0 n * M := by rw [e]; simp
      simp only [transpose_neg, transpose_mul, ht, Matrix.mul_neg, neg_neg, e2]
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, h]; simp

end AdcHSH

end UnQuantumMechanics

open Matrix in
theorem solution (n : ℕ) (S₁ S₂ C₁ C₂ : Matrix (UnQuantumMechanics.PhaseIdx n) (UnQuantumMechanics.PhaseIdx n) ℝ)
    (hS₁ : UnQuantumMechanics.IsHamiltonianMatrix n S₁) (hS₂ : UnQuantumMechanics.IsHamiltonianMatrix n S₂)
    (hC₁ : UnQuantumMechanics.IsSkewHamiltonianMatrix n C₁) (hC₂ : UnQuantumMechanics.IsSkewHamiltonianMatrix n C₂) (k : ℕ) :
    (UnQuantumMechanics.IsHamiltonianMatrix n (S₁ * S₂ - S₂ * S₁) ∧
      UnQuantumMechanics.IsHamiltonianMatrix n (C₁ * C₂ - C₂ * C₁) ∧
      UnQuantumMechanics.IsHamiltonianMatrix n (C₁ * S₁ + S₁ * C₁) ∧
      UnQuantumMechanics.IsHamiltonianMatrix n (S₁ ^ (2 * k + 1))) ∧
    (UnQuantumMechanics.IsSkewHamiltonianMatrix n (S₁ * S₂ + S₂ * S₁) ∧
      UnQuantumMechanics.IsSkewHamiltonianMatrix n (C₁ * C₂ + C₂ * C₁) ∧
      UnQuantumMechanics.IsSkewHamiltonianMatrix n (C₁ * S₁ - S₁ * C₁) ∧
      UnQuantumMechanics.IsSkewHamiltonianMatrix n (S₁ ^ (2 * k)) ∧
      UnQuantumMechanics.IsSkewHamiltonianMatrix n (C₁ ^ k)) := by
  rw [UnQuantumMechanics.AdcHSH.ham_iff] at hS₁ hS₂
  rw [UnQuantumMechanics.AdcHSH.skew_iff] at hC₁ hC₂
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [UnQuantumMechanics.AdcHSH.ham_iff, UnQuantumMechanics.AdcHSH.sig_sub, UnQuantumMechanics.AdcHSH.sig_mul, UnQuantumMechanics.AdcHSH.sig_mul, hS₁, hS₂]; noncomm_ring
  · rw [UnQuantumMechanics.AdcHSH.ham_iff, UnQuantumMechanics.AdcHSH.sig_sub, UnQuantumMechanics.AdcHSH.sig_mul, UnQuantumMechanics.AdcHSH.sig_mul, hC₁, hC₂]; noncomm_ring
  · rw [UnQuantumMechanics.AdcHSH.ham_iff, UnQuantumMechanics.AdcHSH.sig_add, UnQuantumMechanics.AdcHSH.sig_mul, UnQuantumMechanics.AdcHSH.sig_mul, hS₁, hC₁]; noncomm_ring
  · rw [UnQuantumMechanics.AdcHSH.ham_iff, UnQuantumMechanics.AdcHSH.sig_pow, hS₁, Odd.neg_pow (odd_two_mul_add_one k)]
  · rw [UnQuantumMechanics.AdcHSH.skew_iff, UnQuantumMechanics.AdcHSH.sig_add, UnQuantumMechanics.AdcHSH.sig_mul, UnQuantumMechanics.AdcHSH.sig_mul, hS₁, hS₂]; noncomm_ring
  · rw [UnQuantumMechanics.AdcHSH.skew_iff, UnQuantumMechanics.AdcHSH.sig_add, UnQuantumMechanics.AdcHSH.sig_mul, UnQuantumMechanics.AdcHSH.sig_mul, hC₁, hC₂]; abel
  · rw [UnQuantumMechanics.AdcHSH.skew_iff, UnQuantumMechanics.AdcHSH.sig_sub, UnQuantumMechanics.AdcHSH.sig_mul, UnQuantumMechanics.AdcHSH.sig_mul, hS₁, hC₁]; noncomm_ring
  · rw [UnQuantumMechanics.AdcHSH.skew_iff, UnQuantumMechanics.AdcHSH.sig_pow, hS₁, Even.neg_pow (even_two_mul k)]
  · rw [UnQuantumMechanics.AdcHSH.skew_iff, UnQuantumMechanics.AdcHSH.sig_pow, hC₁]
