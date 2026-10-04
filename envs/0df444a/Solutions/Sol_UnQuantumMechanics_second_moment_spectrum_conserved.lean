-- Prove2me | solution 1 for UnQuantumMechanics.second_moment_spectrum_conserved
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:04:35.812862+00:00
-- url     : https://prove2.me/submissions/a88ebca0-2570-43d7-8771-9f3d78affc1e

import Mathlib
import Definitions.Def_UnQM_phase_space

set_option autoImplicit false

namespace UnQMSecondMoment

open Matrix UnQuantumMechanics
open scoped Kronecker

lemma eta0_sq : eta0 * eta0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta0, Matrix.mul_apply, Fin.sum_univ_two]

lemma gamma0_sq (n : ℕ) : gamma0 n * gamma0 n = -1 := by
  unfold gamma0
  change (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ eta0 * ((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ eta0) = -1
  rw [← Matrix.mul_kronecker_mul, eta0_sq, Matrix.one_mul]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [kroneckerMap_apply, Matrix.neg_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : i = j <;> by_cases h2 : a = b <;> simp [h1, h2]

lemma gamma0_T (n : ℕ) : (gamma0 n)ᵀ = -gamma0 n := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [transpose_apply, Matrix.neg_apply, gamma0, kroneckerMap_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    fin_cases a <;> fin_cases b <;> simp [eta0]
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']

lemma gamma0_sq_mul (n : ℕ) (X : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) :
    gamma0 n * (gamma0 n * X) = -X := by
  rw [← Matrix.mul_assoc, gamma0_sq, Matrix.neg_mul, Matrix.one_mul]

lemma conj_pow_aux {R : Type*} [Monoid R] (P Q X : R) (h1 : Q * P = 1) (h2 : P * Q = 1) :
    ∀ m : ℕ, (P * X * Q) ^ m = P * X ^ m * Q
  | 0 => by simp [h2]
  | m + 1 => by
    rw [pow_succ, conj_pow_aux P Q X h1 h2 m, pow_succ]
    calc P * X ^ m * Q * (P * X * Q) = P * X ^ m * (Q * P) * X * Q := by simp only [mul_assoc]
      _ = P * (X ^ m * X) * Q := by rw [h1]; simp only [mul_one, mul_assoc]

section analysis

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma hasDerivAt_of_entries {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ℝ → Matrix ι ι ℝ} {F' : Matrix ι ι ℝ} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun s => F s i j) (F' i j) t) : HasDerivAt F F' t := by
  have key : ∀ M : Matrix ι ι ℝ, M = ∑ i, ∑ j, M i j • Matrix.single i j (1 : ℝ) := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp [Matrix.smul_single]
  have hs : HasDerivAt (fun s => ∑ i, ∑ j, F s i j • Matrix.single i j (1 : ℝ))
      (∑ i, ∑ j, F' i j • Matrix.single i j (1 : ℝ)) t :=
    HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun j _ => (h i j).smul_const _))
  rw [← key F'] at hs
  convert hs using 1
  funext s
  exact key (F s)

set_option backward.isDefEq.respectTransparency false in
lemma charpoly_conserved (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ)
    (hH : IsHamiltonianMatrix n H)
    (Sig : ℝ → Matrix (PhaseIdx n) (PhaseIdx n) ℝ)
    (hSig : ∀ τ i j, HasDerivAt (fun t => Sig t i j) ((H * Sig τ + Sig τ * Hᵀ) i j) τ)
    (τ : ℝ) :
    (autocorr n (Sig τ)).charpoly = (autocorr n (Sig 0)).charpoly := by
  set S : ℝ → Matrix (PhaseIdx n) (PhaseIdx n) ℝ := fun t => autocorr n (Sig t) with hSdef
  have hS : ∀ t, HasDerivAt S (H * S t - S t * H) t := by
    intro t
    have h1 := (hasDerivAt_of_entries (hSig t)).mul_const ((gamma0 n)ᵀ)
    have heq : (H * Sig t + Sig t * Hᵀ) * (gamma0 n)ᵀ = H * S t - S t * H := by
      obtain ⟨A, hA, rfl⟩ := hH
      simp only [hSdef, autocorr, Matrix.transpose_mul, hA.eq, gamma0_T]
      simp only [Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
        gamma0_sq_mul, gamma0_sq, Matrix.mul_one, neg_neg]
      abel
    exact h1.congr_deriv heq
  set U : ℝ → Matrix (PhaseIdx n) (PhaseIdx n) ℝ :=
    fun t => NormedSpace.exp (t • (-H)) * S t * NormedSpace.exp (t • H) with hUdef
  have hU : ∀ t, HasDerivAt U 0 t := by
    intro t
    have e1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-H) t
    have e2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) H t
    have := (e1.mul (hS t)).mul e2
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply]
    noncomm_ring
  have hconst : U τ = U 0 :=
    is_const_of_deriv_eq_zero (fun t => (hU t).differentiableAt) (fun t => (hU t).deriv) τ 0
  have hU0 : U 0 = S 0 := by
    simp [hUdef, NormedSpace.exp_zero]
  have hE : NormedSpace.exp (τ • (-H)) * NormedSpace.exp (τ • H) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl H).neg_left.smul_left τ).smul_right τ)]
    simp
  have hE' : NormedSpace.exp (τ • H) * NormedSpace.exp (τ • (-H)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl H).neg_right.smul_left τ).smul_right τ)]
    simp
  have hSτ : S τ = NormedSpace.exp (τ • H) * (S 0 * NormedSpace.exp (τ • (-H))) := by
    rw [← hU0, ← hconst]
    simp only [hUdef, ← Matrix.mul_assoc, hE', Matrix.one_mul]
    rw [Matrix.mul_assoc, hE', Matrix.mul_one]
  change (S τ).charpoly = (S 0).charpoly
  rw [hSτ, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hE, Matrix.mul_one]

end analysis

lemma odd_trace_zero (n : ℕ) (Sg : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hSym : Sg.IsSymm)
    (k : ℕ) : (autocorr n Sg ^ (2 * k + 1)).trace = 0 := by
  set S := autocorr n Sg with hSdef
  have hT : Sᵀ = gamma0 n * (-S) * (gamma0 n)ᵀ := by
    simp only [hSdef, autocorr, Matrix.transpose_mul, Matrix.transpose_neg, hSym.eq, gamma0_T, neg_neg]
    simp only [Matrix.mul_assoc, Matrix.mul_neg, neg_neg, gamma0_sq,
      Matrix.mul_one]
  have h1 : (gamma0 n)ᵀ * gamma0 n = 1 := by
    rw [gamma0_T, Matrix.neg_mul, gamma0_sq, neg_neg]
  have h2 : gamma0 n * (gamma0 n)ᵀ = 1 := by
    rw [gamma0_T, Matrix.mul_neg, gamma0_sq, neg_neg]
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  have key : (S ^ (2 * k + 1)).trace = -(S ^ (2 * k + 1)).trace := by
    calc (S ^ (2 * k + 1)).trace = ((S ^ (2 * k + 1))ᵀ).trace := (Matrix.trace_transpose _).symm
      _ = ((gamma0 n * (-S) * (gamma0 n)ᵀ) ^ (2 * k + 1)).trace := by
          rw [Matrix.transpose_pow, hT]
      _ = (gamma0 n * (-S) ^ (2 * k + 1) * (gamma0 n)ᵀ).trace := by
          rw [conj_pow_aux _ _ _ h1 h2]
      _ = ((-S) ^ (2 * k + 1)).trace := by
          rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = -(S ^ (2 * k + 1)).trace := by
          rw [hodd.neg_pow, Matrix.trace_neg]
  linarith

end UnQMSecondMoment

open Matrix UnQuantumMechanics in
theorem solution (n : ℕ) (H : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) (hH : IsHamiltonianMatrix n H)
    (Sig : ℝ → Matrix (PhaseIdx n) (PhaseIdx n) ℝ)
    (hSig : ∀ τ i j, HasDerivAt (fun t => Sig t i j) ((H * Sig τ + Sig τ * Hᵀ) i j) τ)
    (hSym : ∀ t, (Sig t).IsSymm) (τ : ℝ) :
    (autocorr n (Sig τ)).charpoly = (autocorr n (Sig 0)).charpoly ∧
      ∀ k : ℕ, (autocorr n (Sig τ) ^ (2 * k + 1)).trace = 0 := by
  exact ⟨UnQMSecondMoment.charpoly_conserved n H hH Sig hSig τ,
    fun k => UnQMSecondMoment.odd_trace_zero n (Sig τ) (hSym τ) k⟩
