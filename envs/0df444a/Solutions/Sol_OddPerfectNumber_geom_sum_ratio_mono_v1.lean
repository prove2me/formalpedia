-- Prove2me | solution 1 for OddPerfectNumber.geom_sum_ratio_mono_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T07:43:46.479989+00:00
-- url     : https://prove2.me/submissions/7692111b-b977-4b6f-9086-9ba56db0eb70

import Mathlib

theorem solution (b k n : Nat) (hb : 2 ≤ b) (hkn : k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), b ^ i) * b ^ n ≤
      (∑ i ∈ Finset.range (n + 1), b ^ i) * b ^ k := by
  have hb1 : (1:ℚ) ≤ (b:ℚ) := by exact_mod_cast (by omega : 1 ≤ b)
  have hpos : (0:ℚ) < (b:ℚ) - 1 := by
    have h1 : (1:ℚ) < (b:ℚ) := by exact_mod_cast (by omega : 1 < b)
    linarith
  have hne : ((b:ℚ) - 1) ≠ 0 := ne_of_gt hpos
  have closed : ∀ t : Nat, (∑ i ∈ Finset.range (t + 1), (b:ℚ) ^ i) * ((b:ℚ) - 1)
      = (b:ℚ) ^ (t + 1) - 1 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      have hB : (b:ℚ) ^ (t + 1) * ((b:ℚ) - 1) = (b:ℚ) ^ (t + 1 + 1) - (b:ℚ) ^ (t + 1) := by
        ring
      rw [hB]
      ring
  have e1 : (∑ i ∈ Finset.range (k + 1), (b:ℚ) ^ i)
      = ((b:ℚ) ^ (k + 1) - 1) / ((b:ℚ) - 1) := by
    rw [eq_div_iff hne]
    have h := closed k
    linarith [h]
  have e2 : (∑ i ∈ Finset.range (n + 1), (b:ℚ) ^ i)
      = ((b:ℚ) ^ (n + 1) - 1) / ((b:ℚ) - 1) := by
    rw [eq_div_iff hne]
    have h := closed n
    linarith [h]
  have hpow : (b:ℚ) ^ k ≤ (b:ℚ) ^ n := pow_le_pow_right₀ hb1 hkn
  have hq : (∑ i ∈ Finset.range (k + 1), (b:ℚ) ^ i) * (b:ℚ) ^ n ≤
      (∑ i ∈ Finset.range (n + 1), (b:ℚ) ^ i) * (b:ℚ) ^ k := by
    rw [e1, e2, div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
    have e3 : ((b:ℚ) ^ (k + 1) - 1) * (b:ℚ) ^ n = (b:ℚ) ^ (k + 1 + n) - (b:ℚ) ^ n := by
      ring
    have e4 : ((b:ℚ) ^ (n + 1) - 1) * (b:ℚ) ^ k = (b:ℚ) ^ (n + 1 + k) - (b:ℚ) ^ k := by
      ring
    rw [e3, e4]
    have e5 : (b:ℚ) ^ (k + 1 + n) = (b:ℚ) ^ (n + 1 + k) := by ring
    rw [e5]
    linarith [hpow]
  have hcast1 : ((∑ i ∈ Finset.range (k + 1), b ^ i) : ℚ)
      = ∑ i ∈ Finset.range (k + 1), (b:ℚ) ^ i := by
    push_cast
    ring
  have hcast2 : ((∑ i ∈ Finset.range (n + 1), b ^ i) : ℚ)
      = ∑ i ∈ Finset.range (n + 1), (b:ℚ) ^ i := by
    push_cast
    ring
  have hq2 : (((∑ i ∈ Finset.range (k + 1), b ^ i) * b ^ n : Nat) : ℚ) ≤
      (((∑ i ∈ Finset.range (n + 1), b ^ i) * b ^ k : Nat) : ℚ) := by
    push_cast
    rw [hcast1, hcast2]
    exact hq
  exact_mod_cast hq2
