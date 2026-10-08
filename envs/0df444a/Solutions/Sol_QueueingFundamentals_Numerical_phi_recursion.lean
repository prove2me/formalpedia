-- Prove2me | solution 1 for QueueingFundamentals.Numerical.phi_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:32:05.336468+00:00
-- url     : https://prove2.me/submissions/a12a62b7-930b-4305-8baa-63387cc563c8

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_Uniformization

open Matrix

namespace QueueingFundamentals.Numerical

theorem p33_rowsum_zero {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (i : Fin (N + 1)) : ∑ j, Q i j = 0 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hQ.2 i]
  ring

theorem p33_stoch {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (Λ : ℝ) (hΛ : 0 < Λ) (hΛq : ∀ i, exitRate Q i ≤ Λ) :
    IsStochastic (uniformizedMatrix Λ Q) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [uniformizedMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      have h1 := hΛq i
      simp only [exitRate] at h1
      have : -(Λ⁻¹ * Q i i) ≤ 1 := by
        rw [show -(Λ⁻¹ * Q i i) = (-Q i i) / Λ by ring, div_le_one hΛ]
        exact h1
      linarith
    · simp only [h, if_false, add_zero]
      exact mul_nonneg (inv_nonneg.mpr hΛ.le) (hQ.1 i j h)
  · simp only [uniformizedMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Finset.sum_add_distrib, ← Finset.mul_sum, p33_rowsum_zero Q hQ i,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

theorem p33_vecMul_prob {N : ℕ} (P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hP : IsStochastic P) (p : Fin (N + 1) → ℝ) (hp : IsProbVec p) :
    IsProbVec (p ᵥ* P) := by
  refine ⟨fun j => ?_, ?_⟩
  · simp only [Matrix.vecMul, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (hP.1 i j)
  · simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hP.2, mul_one]
    exact hp.2

end QueueingFundamentals.Numerical

open Matrix QueueingFundamentals.Numerical in
theorem solution {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (Λ : ℝ) (hΛ : 0 < Λ) (hΛq : ∀ i, exitRate Q i ≤ Λ)
    (p₀ : Fin (N + 1) → ℝ) (hp₀ : IsProbVec p₀) :
    (∀ k : ℕ, 1 ≤ k → phi Λ Q p₀ k = phi Λ Q p₀ (k - 1) ᵥ* uniformizedMatrix Λ Q) ∧
      ∀ k : ℕ, IsProbVec (phi Λ Q p₀ k) := by
  refine ⟨fun k hk => ?_, fun k => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [phi, Nat.add_sub_cancel, pow_succ, Matrix.vecMul_vecMul]
  · induction k with
    | zero => simpa [phi] using hp₀
    | succ m ih =>
      have : phi Λ Q p₀ (m + 1) = phi Λ Q p₀ m ᵥ* uniformizedMatrix Λ Q := by
        simp only [phi, pow_succ, Matrix.vecMul_vecMul]
      rw [this]
      exact p33_vecMul_prob _ (p33_stoch Q hQ Λ hΛ hΛq) _ ih
