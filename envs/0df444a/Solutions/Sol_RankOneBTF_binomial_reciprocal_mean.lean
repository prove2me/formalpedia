-- Prove2me | solution 1 for RankOneBTF.binomial_reciprocal_mean
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:39:35.236513+00:00
-- url     : https://prove2.me/submissions/1e71d692-3b86-44b9-9d90-c08916421838

import Mathlib

theorem solution (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∑ k ∈ Finset.range (N + 1),
        (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) / (1 + (k : ℝ)) =
      1 / (((N : ℝ) + 1) * q) * (1 - (1 - q) ^ (N + 1)) := by
  have hbin : ∑ k ∈ Finset.range (N + 1),
      ((N + 1).choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (N - k) = 1 - (1 - q) ^ (N + 1) := by
    have h := add_pow q (1 - q) (N + 1)
    have e : q + (1 - q) = 1 := by ring
    rw [e, one_pow, Finset.sum_range_succ'] at h
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one,
      Nat.sub_zero] at h
    have hc : ∀ k ∈ Finset.range (N + 1),
        q ^ (k + 1) * (1 - q) ^ (N + 1 - (k + 1)) * ((N + 1).choose (k + 1) : ℝ) =
          ((N + 1).choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (N - k) := by
      intro k _
      rw [Nat.add_sub_add_right]
      ring
    rw [Finset.sum_congr rfl hc] at h
    linarith
  rw [← hbin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : ((N : ℝ) + 1) * (N.choose k : ℝ) = ((N + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq N k
  have hk : (0 : ℝ) < 1 + k := by positivity
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hr : (N.choose k : ℝ) / (1 + k) = ((N + 1).choose (k + 1) : ℝ) / (N + 1) := by
    rw [div_eq_div_iff hk.ne' hN.ne']
    linarith
  calc (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) / (1 + (k : ℝ))
      = ((N.choose k : ℝ) / (1 + k)) * q ^ k * (1 - q) ^ (N - k) := by ring
    _ = (((N + 1).choose (k + 1) : ℝ) / (N + 1)) * q ^ k * (1 - q) ^ (N - k) := by rw [hr]
    _ = 1 / (((N : ℝ) + 1) * q) *
          (((N + 1).choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (N - k)) := by
        have hq : q ≠ 0 := hq0.ne'
        have hN' : (N : ℝ) + 1 ≠ 0 := hN.ne'
        field_simp
        ring
