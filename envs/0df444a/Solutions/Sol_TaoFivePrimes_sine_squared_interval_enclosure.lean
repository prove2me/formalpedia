-- Prove2me | solution 1 for TaoFivePrimes.sine_squared_interval_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:34:40.555556+00:00
-- url     : https://prove2.me/submissions/6eca57ad-ca2d-421b-b49e-f67ba225b62e

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

private lemma sin_sq_lipschitz (x y : ℝ) :
    |(Real.sin x)^2 - (Real.sin y)^2| ≤ |x-y| := by
  have hid : (Real.sin x)^2 - (Real.sin y)^2 =
      (Real.cos (2*y)-Real.cos (2*x))/2 := by
    rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
    ring
  have h := Real.abs_cos_sub_cos_le (2*y) (2*x)
  have habs : |2*y-2*x| = 2*|x-y| := by
    rw [show 2*y-2*x = -(2*(x-y)) by ring, abs_neg, abs_mul]
    norm_num
  rw [habs] at h
  rw [hid, abs_div]
  norm_num
  linarith

theorem solution (x m lo hi δ : ℝ) (k : ℕ)
    (hx : |x-m| ≤ δ) (hlo0 : 0 ≤ lo)
    (hlo : lo ≤ |m-(k:ℝ)*Real.pi|) (hhi : |m-(k:ℝ)*Real.pi| ≤ hi)
    (hhi1 : hi ≤ 1) :
    (Real.sin x)^2 ≤ (hi-lo^3/6+hi^5/100)^2 + δ := by
  let t : ℝ := m-(k:ℝ)*Real.pi
  have htlo : lo ≤ |t| := hlo
  have hthi : |t| ≤ hi := hhi
  have ht1 : |t| ≤ 1 := hthi.trans hhi1
  have hperiod : (Real.sin t)^2 = (Real.sin m)^2 := by
    dsimp [t]
    rw [Real.sin_sub_nat_mul_pi, mul_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have hbase : |t-t^3/6| = |t|-|t|^3/6 := by
    have hsq : t^2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
    have hc : 0 ≤ 1-t^2/6 := by nlinarith
    rw [show t-t^3/6=t*(1-t^2/6) by ring, abs_mul, abs_of_nonneg hc, ← sq_abs t]
    ring
  have hsin : |Real.sin t| ≤ hi-lo^3/6+hi^5/100 := by
    have hh := Real.sin_bound ht1
    have htri := abs_add_le (Real.sin t-(t-t^3/6)) (t-t^3/6)
    have he : Real.sin t-(t-t^3/6)+(t-t^3/6) = Real.sin t := by ring
    rw [he,hbase] at htri
    have hcub := pow_le_pow_left₀ hlo0 htlo 3
    have hfifth := pow_le_pow_left₀ (abs_nonneg t) hthi 5
    nlinarith only [hh,htri,hcub,hfifth,hthi]
  have hs2 : (Real.sin t)^2 ≤ (hi-lo^3/6+hi^5/100)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (Real.sin t)) hsin 2
    simpa only [sq_abs] using hh
  have hdist := sin_sq_lipschitz x m
  have hupper := (abs_le.mp hdist).2
  rw [hperiod] at hs2
  linarith
