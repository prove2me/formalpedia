-- Prove2me | solution 2 for TaoFivePrimes.dusart_envelope_log_four_comparison
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T02:26:36.249699+00:00
-- url     : https://prove2.me/submissions/5a346a70-30c7-4359-b735-9a352886fc6a

import Mathlib
set_option autoImplicit false

private lemma tail_exp_comparison (u : ℝ) (hu : 49 ≤ u) :
    2592 * u ^ 9 ≤ (1513 / 10 : ℝ) * Real.exp u := by
  have hu0 : 0 ≤ u := by linarith
  have hp : (49 : ℝ)^15 ≤ u^15 := pow_le_pow_left₀ (by norm_num) hu 15
  have he := Real.pow_div_factorial_le_exp u hu0 24
  norm_num [Nat.factorial] at he
  have hpow : u^24 = u^15 * u^9 := by ring
  have hnum : 2592 * u^9 ≤ (1513 / 10 : ℝ) * (u^24 / 620448401733239439360000) := by
    rw [hpow]
    have := mul_le_mul_of_nonneg_right hp (pow_nonneg hu0 9)
    nlinarith [pow_nonneg hu0 9]
  exact hnum.trans (mul_le_mul_of_nonneg_left he (by norm_num))

theorem solution (t : ℝ) (ht : 13900 ≤ t) :
    Real.sqrt (8 / Real.pi) *
      Real.sqrt (Real.sqrt (t / (569693 / 100000 : ℝ))) *
      Real.exp (-Real.sqrt (t / (569693 / 100000 : ℝ))) ≤
      (1513 / 10 : ℝ) / t ^ 4 := by
  let u := Real.sqrt (t / (569693 / 100000 : ℝ))
  have ht0 : 0 < t := by linarith
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = t / (569693 / 100000 : ℝ) := Real.sq_sqrt (by positivity)
  have hu : 49 ≤ u := by
    nlinarith
  have htu : t ≤ 6 * u^2 := by nlinarith
  have hpow : t^4 ≤ (6*u^2)^4 := pow_le_pow_left₀ (le_of_lt ht0) htu 4
  have hs : Real.sqrt u ≤ u := by
    have hh := Real.sq_sqrt hu0
    have hn := Real.sqrt_nonneg u
    nlinarith
  have hpi : Real.sqrt (8 / Real.pi) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · apply (div_le_iff₀ Real.pi_pos).2
      nlinarith [Real.pi_gt_three]
  have hfactor : Real.sqrt (8 / Real.pi) * Real.sqrt u * t^4 ≤ 2592*u^9 := by
    calc
      _ ≤ (2*u)*t^4 := mul_le_mul_of_nonneg_right
        (mul_le_mul hpi hs (Real.sqrt_nonneg _) (by norm_num)) (by positivity)
      _ ≤ (2*u)*(6*u^2)^4 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have he := tail_exp_comparison u hu
  have hprod : Real.sqrt (8 / Real.pi) * Real.sqrt u * t^4 ≤
      (1513/10:ℝ) * Real.exp u := hfactor.trans he
  change Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤ _
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos ht0 4)).2
  have hh := (div_le_iff₀ (Real.exp_pos u)).2 hprod
  convert hh using 1 <;> ring

