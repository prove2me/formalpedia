-- Prove2me | solution 1 for ShallowSym.factorial_ratio
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T15:23:57.707137+00:00
-- url     : https://prove2.me/submissions/5c3b1a20-b65b-42ae-aaee-08ee4382a9f0

import Mathlib

/-- Shallow circuits for majority: `k! / k^{k-1} ≥ e^{-k}` for every `k ≥ 1`. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (-(k : ℝ)) ≤ (k.factorial : ℝ) / (k : ℝ) ^ (k - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hpow : 0 < (k : ℝ) ^ k := pow_pos hk0 k
  have h := Real.pow_div_factorial_le_exp (k : ℝ) hk0.le k
  have h1 : Real.exp (-(k : ℝ)) ≤ (k.factorial : ℝ) / (k : ℝ) ^ k := by
    have hmul : 1 ≤ Real.exp (k : ℝ) * ((k.factorial : ℝ) / (k : ℝ) ^ k) := by
      have hm := mul_le_mul_of_nonneg_right h (le_of_lt (div_pos hfac hpow))
      have hs : ((k : ℝ) ^ k / (k.factorial : ℝ)) *
          ((k.factorial : ℝ) / (k : ℝ) ^ k) = 1 := by
        field_simp
      linarith
    have hmul' : 1 ≤ ((k.factorial : ℝ) / (k : ℝ) ^ k) * Real.exp (k : ℝ) := by
      rwa [mul_comm] at hmul
    rw [Real.exp_neg]
    exact (inv_le_iff_one_le_mul₀ (Real.exp_pos (k : ℝ))).mpr hmul'
  have hpowle : (k : ℝ) ^ (k - 1) ≤ (k : ℝ) ^ k := by
    have hstep : (k : ℝ) ^ (k - 1) * 1 ≤ (k : ℝ) ^ (k - 1) * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hk1 (pow_nonneg hk0.le _)
    have heq : (k : ℝ) ^ k = (k : ℝ) ^ (k - 1) * (k : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    linarith
  calc Real.exp (-(k : ℝ)) ≤ (k.factorial : ℝ) / (k : ℝ) ^ k := h1
    _ ≤ (k.factorial : ℝ) / (k : ℝ) ^ (k - 1) := by
      rw [div_le_div_iff₀ hpow (pow_pos hk0 _)]
      nlinarith [hfac.le, hpowle]
