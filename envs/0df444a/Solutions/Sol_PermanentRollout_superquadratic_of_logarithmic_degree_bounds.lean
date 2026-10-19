-- Prove2me | solution 1 for PermanentRollout.superquadratic_of_logarithmic_degree_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/441e878c-ccf8-4e50-8269-1466935daae8

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution
    (complexity : ℕ → ℕ)
    (bound : ∀ d : ℕ, 3 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) - 1) / 144 ≤ complexity n) :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n : ℝ) ^ 2 ≤ complexity n := by
  intro C hC
  obtain ⟨k, hk⟩ := exists_nat_gt (144 * C + 1)
  have hk_ne : k ≠ 0 := by
    intro hzero
    subst k
    norm_num at hk
    nlinarith
  have hpower : 1 < (2 : ℕ) ^ k := one_lt_pow₀ (by norm_num) hk_ne
  have hdegree : 3 ≤ 2 ^ k + 1 := by omega
  obtain ⟨N, hN⟩ := bound (2 ^ k + 1) hdegree
  refine ⟨N, fun n hn => ?_⟩
  have hlog : Real.logb 2 (((2 ^ k + 1 : ℕ) : ℝ) - 1) = (k : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_pow, Real.logb_pow]
  have hcoefficient : C ≤ (k : ℝ) / 144 := by nlinarith
  calc
    C * (n : ℝ) ^ 2 ≤ ((k : ℝ) / 144) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg (n : ℝ))
    _ = (n : ℝ) ^ 2 * (k : ℝ) / 144 := by ring
    _ ≤ complexity n := by
      have hbound := hN n hn
      rw [hlog] at hbound
      exact hbound
end PermanentRollout
