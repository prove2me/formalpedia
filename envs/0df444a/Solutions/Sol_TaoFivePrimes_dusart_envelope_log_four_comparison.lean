-- Prove2me | solution 1 for TaoFivePrimes.dusart_envelope_log_four_comparison
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T20:19:23.60453+00:00
-- url     : https://prove2.me/submissions/32cd1a79-09ac-4589-8c61-5eddfe1c444c

import Mathlib


namespace TaoEnvelope

lemma exp_dominates_ninth_power {u : ℝ} (hu : 49 ≤ u) : 18 * u ^ 9 ≤ Real.exp u := by
  have hu0 : 0 ≤ u := by linarith
  have hc : (18 : ℝ) * (Nat.factorial 24 : ℝ) ≤ 49 ^ 15 := by norm_num
  have hp : (18 : ℝ) * (Nat.factorial 24 : ℝ) ≤ u ^ 15 :=
    hc.trans (pow_le_pow_left₀ (by norm_num) hu 15)
  have hmul := mul_le_mul_of_nonneg_right hp (pow_nonneg hu0 9)
  have hfact : (0 : ℝ) < (Nat.factorial 24 : ℝ) := by positivity
  apply le_trans ((le_div_iff₀ hfact).mpr ?_) (Real.pow_div_factorial_le_exp u hu0 24)
  calc
    18 * u^9 * (Nat.factorial 24 : ℝ) = 18 * (Nat.factorial 24 : ℝ) * u^9 := by ring
    _ ≤ u^15*u^9 := hmul
    _ = u^24 := by ring

end TaoEnvelope

theorem TaoFivePrimes.dusart_envelope_log_four_comparison (t : ℝ) (ht : 13900 ≤ t) :
    Real.sqrt (8 / Real.pi) *
      Real.sqrt (Real.sqrt (t / (569693 / 100000 : ℝ))) *
      Real.exp (-Real.sqrt (t / (569693 / 100000 : ℝ))) ≤
      (1513 / 10 : ℝ) / t ^ 4 := by
  let R : ℝ := 569693 / 100000
  let u : ℝ := Real.sqrt (t / R)
  have hR : 0 < R := by norm_num [R]
  have hR6 : R ≤ 6 := by norm_num [R]
  have ht0 : 0 < t := by linarith
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = t / R := Real.sq_sqrt (div_nonneg ht0.le hR.le)
  have hu49 : 49 ≤ u := by
    have hh : (49 : ℝ)^2 ≤ t/R := (le_div_iff₀ hR).mpr (by norm_num [R]; linarith)
    nlinarith
  have ht_scale : t = R * u^2 := by rw [husq, mul_div_cancel₀ _ hR.ne']
  have ht_le : t ≤ 6*u^2 := by rw [ht_scale]; nlinarith [sq_nonneg u]
  have ht4 : t^4 ≤ 6^4*u^8 := by
    have h := pow_le_pow_left₀ ht0.le ht_le 4
    simpa only [mul_pow, ← pow_mul] using h
  have hpi : Real.sqrt (8/Real.pi) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.two_le_pi]
  have hsqrt : Real.sqrt u ≤ u := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hexp := TaoEnvelope.exp_dominates_ninth_power hu49
  have hden : 0 < 18*u^9 := by positivity
  have hinv : Real.exp (-u) ≤ 1/(18*u^9) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hden hexp
  change Real.sqrt (8/Real.pi) * Real.sqrt u * Real.exp (-u) ≤ (1513/10:ℝ)/t^4
  calc
    _ ≤ (2*u)*Real.exp (-u) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hpi hsqrt (Real.sqrt_nonneg u) (by norm_num)) (Real.exp_pos _).le
    _ ≤ (2*u)/(18*u^9) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2*u)
    _ ≤ (1513/10:ℝ)/t^4 := by
      apply (div_le_div_iff₀ hden (pow_pos ht0 4)).mpr
      have h := mul_le_mul_of_nonneg_left ht4 (by positivity : 0 ≤ 2*u)
      nlinarith [pow_nonneg hu0 9]

theorem solution (t : ℝ) (ht : 13900 ≤ t) :
    Real.sqrt (8 / Real.pi) *
      Real.sqrt (Real.sqrt (t / (569693 / 100000 : ℝ))) *
      Real.exp (-Real.sqrt (t / (569693 / 100000 : ℝ))) ≤
      (1513 / 10 : ℝ) / t ^ 4 :=
  TaoFivePrimes.dusart_envelope_log_four_comparison t ht
