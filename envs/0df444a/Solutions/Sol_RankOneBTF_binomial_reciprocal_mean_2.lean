-- Prove2me | solution 2 for RankOneBTF.binomial_reciprocal_mean
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T15:46:22.908551+00:00
-- url     : https://prove2.me/submissions/5e30690c-9cde-4e22-868d-bc0722ca9014

import Mathlib

/-- Binomial reciprocal identity: `E[1/(1+X)] = (1 - (1-q)^{N+1}) / ((N+1) q)`. -/
theorem solution (N : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∑ k ∈ Finset.range (N + 1),
        (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) / (1 + (k : ℝ)) =
      1 / (((N : ℝ) + 1) * q) * (1 - (1 - q) ^ (N + 1)) := by
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) / (1 + (k : ℝ)) =
        (1 / ((N : ℝ) + 1)) * ((N + 1).choose (k + 1) : ℝ) *
          q ^ k * (1 - q) ^ (N - k) := by
    intro k hk
    have hk1 : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have hchoose : ((N : ℝ) + 1) * (N.choose k : ℝ) =
        ((N + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq N k
    have hratio : (N.choose k : ℝ) / (1 + (k : ℝ)) =
        ((N + 1).choose (k + 1) : ℝ) / ((N : ℝ) + 1) := by
      rw [div_eq_div_iff hk1.ne' hN1]
      linarith
    calc (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) / (1 + (k : ℝ))
        = ((N.choose k : ℝ) / (1 + (k : ℝ))) * q ^ k * (1 - q) ^ (N - k) := by
          ring
      _ = (((N + 1).choose (k + 1) : ℝ) / ((N : ℝ) + 1)) * q ^ k *
            (1 - q) ^ (N - k) := by rw [hratio]
      _ = (1 / ((N : ℝ) + 1)) * ((N + 1).choose (k + 1) : ℝ) *
            q ^ k * (1 - q) ^ (N - k) := by
          field_simp
  rw [Finset.sum_congr rfl hterm]
  have hfactor : ∑ x ∈ Finset.range (N + 1),
        (1 / ((N : ℝ) + 1)) * ((N + 1).choose (x + 1) : ℝ) *
          q ^ x * (1 - q) ^ (N - x) =
      (1 / ((N : ℝ) + 1)) * ∑ x ∈ Finset.range (N + 1),
        ((N + 1).choose (x + 1) : ℝ) * q ^ x * (1 - q) ^ (N - x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hfactor]
  have hstep : ∑ k ∈ Finset.range (N + 1),
        ((N + 1).choose (k + 1) : ℝ) * q ^ k * (1 - q) ^ (N - k) =
      (1 / q) * (1 - (1 - q) ^ (N + 1)) := by
    have hpow := add_pow q (1 - q) (N + 1)
    have hq1q : q + (1 - q) = 1 := by ring
    rw [hq1q, one_pow] at hpow
    have hshift : ∑ k ∈ Finset.range (N + 1),
          ((N + 1).choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (N - k) =
        1 - (1 - q) ^ (N + 1) := by
      have h := Finset.sum_range_succ'
        (fun m => ((N + 1).choose m : ℝ) * q ^ m * (1 - q) ^ (N + 1 - m)) (N + 1)
      have hf0 : ((N + 1).choose 0 : ℝ) * q ^ 0 * (1 - q) ^ (N + 1 - 0) =
          (1 - q) ^ (N + 1) := by
        simp
      rw [hf0] at h
      have hpow' : (1 : ℝ) = ∑ m ∈ Finset.range (N + 2),
          (N + 1).choose m * q ^ m * (1 - q) ^ (N + 1 - m) := by
        conv_lhs => rw [hpow]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      have h2 : (1 : ℝ) = ∑ k ∈ Finset.range (N + 1),
          (N + 1).choose (k + 1) * q ^ (k + 1) * (1 - q) ^ (N + 1 - (k + 1)) +
            (1 - q) ^ (N + 1) := by
        rw [← hpow'] at h
        exact h
      have hcongr : ∑ k ∈ Finset.range (N + 1),
            ((N + 1).choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (N - k) =
          ∑ k ∈ Finset.range (N + 1),
            (N + 1).choose (k + 1) * q ^ (k + 1) * (1 - q) ^ (N + 1 - (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        have : N + 1 - (k + 1) = N - k := by omega
        rw [this]
      rw [hcongr]
      linarith [h2]
    have hmul : ∑ k ∈ Finset.range (N + 1),
          ((N + 1).choose (k + 1) : ℝ) * q ^ k * (1 - q) ^ (N - k) =
        (1 / q) * ∑ k ∈ Finset.range (N + 1),
          ((N + 1).choose (k + 1) : ℝ) * q ^ (k + 1) * (1 - q) ^ (N - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      field_simp
      ring
    rw [hmul, hshift]
  rw [hstep]
  field_simp
