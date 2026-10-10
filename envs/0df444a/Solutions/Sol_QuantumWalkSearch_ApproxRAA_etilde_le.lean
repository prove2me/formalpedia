-- Prove2me | solution 1 for QuantumWalkSearch.ApproxRAA.etilde_le
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T01:05:19.43764+00:00
-- url     : https://prove2.me/submissions/35fc910e-ff77-4d39-ae5b-f53a94c15b93

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit

open QuantumWalkSearch.ApproxRAA

theorem solution (γ φ₀ : ℝ) (hγ : 0 < γ) (hφ₀ : 0 ≤ φ₀) (t : ℕ)
    (ht : (3 : ℝ) ^ t * φ₀ ≤ Real.pi) (i : ℕ) (hi : i ≤ t) :
    etilde γ φ₀ i ≤ γ * ((3 : ℝ) ^ i * φ₀) / Real.pi ∧
      γ * ((3 : ℝ) ^ i * φ₀) / Real.pi ≤ γ := by
  have hpi := Real.pi_pos
  -- closed form of the recursion
  have hclosed : ∀ i : ℕ, etilde γ φ₀ i =
      (3 : ℝ) ^ i * φ₀ * (6 * γ / Real.pi ^ 3) *
        ∑ k ∈ Finset.range i, 1 / ((k : ℝ) + 1) ^ 2 := by
    intro i
    induction i with
    | zero => simp [etilde]
    | succ i ih =>
      rw [show etilde γ φ₀ (i + 1) =
          4 * beta γ (i + 1) * ((3 : ℝ) ^ i * φ₀) + 3 * etilde γ φ₀ i from rfl, ih,
        Finset.sum_range_succ]
      unfold beta
      push_cast
      field_simp
      try ring
  -- Basel bound for the partial sums
  have hS : ∀ i : ℕ, ∑ k ∈ Finset.range i, 1 / ((k : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    intro i
    have h := sum_le_hasSum (Finset.range (i + 1)) (fun n _ => by positivity) hasSum_zeta_two
    rw [Finset.sum_range_succ'] at h
    simpa using h
  constructor
  · rw [hclosed]
    have h3 : 0 ≤ (3 : ℝ) ^ i * φ₀ * (6 * γ / Real.pi ^ 3) := by positivity
    calc (3 : ℝ) ^ i * φ₀ * (6 * γ / Real.pi ^ 3) * ∑ k ∈ Finset.range i, 1 / ((k : ℝ) + 1) ^ 2
        ≤ (3 : ℝ) ^ i * φ₀ * (6 * γ / Real.pi ^ 3) * (Real.pi ^ 2 / 6) :=
          mul_le_mul_of_nonneg_left (hS i) h3
      _ = γ * ((3 : ℝ) ^ i * φ₀) / Real.pi := by field_simp; try ring
  · have h3i : (3 : ℝ) ^ i * φ₀ ≤ Real.pi := by
      calc (3 : ℝ) ^ i * φ₀ ≤ (3 : ℝ) ^ t * φ₀ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) hφ₀
        _ ≤ Real.pi := ht
    rw [div_le_iff₀ hpi]
    nlinarith
