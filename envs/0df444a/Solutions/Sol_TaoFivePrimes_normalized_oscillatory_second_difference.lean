-- Prove2me | solution 1 for TaoFivePrimes.normalized_oscillatory_second_difference
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:28:56.546777+00:00
-- url     : https://prove2.me/submissions/08c81f50-cf30-4d7c-9d8b-383c8dc146d6

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0

private lemma second_difference (A B C : ℂ) (θ ep em : ℝ)
    (hp : ‖A - B*Complex.exp ((θ:ℂ)*Complex.I)‖ ≤ ep)
    (hm : ‖C - B*Complex.exp (((-θ:ℝ):ℂ)*Complex.I)‖ ≤ em) :
    ‖A - 2*B + C‖ ≤ ep + em + 4*‖B‖*(Real.sin (θ/2))^2 := by
  have hc : Real.cos θ = 1 - 2*(Real.sin (θ/2))^2 := by
    have h := Real.cos_two_mul_eq_one_sub (θ/2)
    convert h using 1 <;> ring
  have he : Complex.exp ((θ:ℂ)*Complex.I) +
      Complex.exp (((-θ:ℝ):ℂ)*Complex.I) - 2 =
      ((-4*(Real.sin (θ/2))^2:ℝ):ℂ) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, hc]
    push_cast
    ring
  have hn : ‖Complex.exp ((θ:ℂ)*Complex.I) +
      Complex.exp (((-θ:ℝ):ℂ)*Complex.I) - 2‖ = 4*(Real.sin (θ/2))^2 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (show -4*(Real.sin (θ/2))^2 ≤ 0 by nlinarith [sq_nonneg (Real.sin (θ/2))])]
    ring
  have hid : A - 2*B + C =
      (A - B*Complex.exp ((θ:ℂ)*Complex.I)) +
      (C - B*Complex.exp (((-θ:ℝ):ℂ)*Complex.I)) +
      B*(Complex.exp ((θ:ℂ)*Complex.I) +
        Complex.exp (((-θ:ℝ):ℂ)*Complex.I) - 2) := by ring
  rw [hid]
  have h1 := norm_add_le (A - B*Complex.exp ((θ:ℂ)*Complex.I))
    (C - B*Complex.exp (((-θ:ℝ):ℂ)*Complex.I))
  have h2 := norm_add_le
    ((A - B*Complex.exp ((θ:ℂ)*Complex.I)) +
      (C - B*Complex.exp (((-θ:ℝ):ℂ)*Complex.I)))
    (B*(Complex.exp ((θ:ℂ)*Complex.I) +
      Complex.exp (((-θ:ℝ):ℂ)*Complex.I) - 2))
  rw [norm_mul, hn] at h2
  nlinarith only [hp, hm, h1, h2]

private lemma log_phase_errors (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/3) :
    |Real.log (1+r)-r| + |Real.log (1-r)+r| ≤ 3*r^2 := by
  have hr : |r| < 1 := by rw [abs_of_nonneg hr0]; linarith
  have hnr : |-r| < 1 := by simpa only [abs_neg] using hr
  have hn := Real.abs_log_sub_add_sum_range_le hr 1
  have hp := Real.abs_log_sub_add_sum_range_le hnr 1
  have hminus : |Real.log (1-r)+r| ≤ r^2/(1-r) := by
    simpa [Finset.sum_range_succ, abs_of_nonneg hr0, add_comm] using hn
  have hplus : |Real.log (1+r)-r| ≤ r^2/(1-r) := by
    simpa [Finset.sum_range_succ, abs_of_nonneg hr0, abs_of_nonpos (neg_nonpos.mpr hr0),
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hp
  have hpos : 0 < 1-r := by linarith
  have hb : 2*(r^2/(1-r)) ≤ 3*r^2 := by
    rw [show 2*(r^2/(1-r)) = (2*r^2)/(1-r) by ring]
    apply (div_le_iff₀ hpos).2
    have hm := mul_nonneg (sq_nonneg r) (show 0 ≤ 1-3*r by linarith)
    nlinarith only [hm]
  linarith

private lemma power_amplitude_errors (r α : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/3)
    (ha0 : 0 ≤ α) (ha3 : α ≤ 3) :
    |(1+r)^α-1| + |(1-r)^α-1| ≤ 8*r := by
  have hp0 : 1 ≤ (1+r)^α := Real.one_le_rpow (by linarith) ha0
  have hm0 : (1-r)^α ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) ha0
  have hp : (1+r)^α ≤ (1+r)^3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 1+r by linarith) ha3
    simpa only [Real.rpow_ofNat] using h
  have hm : (1-r)^3 ≤ (1-r)^α := by
    have h := Real.rpow_le_rpow_of_exponent_ge (show (0:ℝ) < 1-r by linarith)
      (show 1-r ≤ 1 by linarith) ha3
    simpa only [Real.rpow_ofNat] using h
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have hsq : r^2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hh := mul_nonneg hr0 (sub_nonneg.mpr hsq)
  nlinarith only [hp,hm,hh]


private lemma unit_phase_distance (x y : ℝ) :
    ‖Complex.exp ((x:ℂ)*Complex.I)-Complex.exp ((y:ℂ)*Complex.I)‖ ≤ |x-y| := by
  have harg : (y:ℂ)*Complex.I + ((x-y:ℝ):ℂ)*Complex.I = (x:ℂ)*Complex.I := by
    push_cast
    ring
  have he : Complex.exp ((x:ℂ)*Complex.I)-Complex.exp ((y:ℂ)*Complex.I) =
      Complex.exp ((y:ℂ)*Complex.I)*
        (Complex.exp (((x-y:ℝ):ℂ)*Complex.I)-1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, harg]
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=x-y))

private lemma amplitude_phase_distance (u x y : ℝ) :
    ‖(u:ℂ)*Complex.exp ((x:ℂ)*Complex.I)-Complex.exp ((y:ℂ)*Complex.I)‖ ≤
      |u-1|+|x-y| := by
  have he : (u:ℂ)*Complex.exp ((x:ℂ)*Complex.I)-Complex.exp ((y:ℂ)*Complex.I) =
      ((u-1:ℝ):ℂ)*Complex.exp ((x:ℂ)*Complex.I)+
        (Complex.exp ((x:ℂ)*Complex.I)-Complex.exp ((y:ℂ)*Complex.I)) := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖((u-1:ℝ):ℂ)*Complex.exp ((x:ℂ)*Complex.I)‖ +
        ‖Complex.exp ((x:ℂ)*Complex.I)-Complex.exp ((y:ℂ)*Complex.I)‖ := norm_add_le _ _
    _ ≤ |u-1|+|x-y| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
      linarith [unit_phase_distance x y]

theorem solution (r α γ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/3)
    (ha0 : 0 ≤ α) (ha3 : α ≤ 3) :
    ‖(((1+r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1+r):ℝ):ℂ)*Complex.I)-2+
      (((1-r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1-r):ℝ):ℂ)*Complex.I)‖ ≤
      4*(Real.sin (γ*r/2))^2 + 8*r + 3 * |γ| * r^2 := by
  let A : ℂ := (((1+r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1+r):ℝ):ℂ)*Complex.I)
  let C : ℂ := (((1-r)^α:ℝ):ℂ)*Complex.exp (((γ*Real.log (1-r):ℝ):ℂ)*Complex.I)
  have hp : ‖A-Complex.exp (((γ*r:ℝ):ℂ)*Complex.I)‖ ≤
      |(1+r)^α-1| + |γ| * |Real.log (1+r)-r| := by
    have h := amplitude_phase_distance ((1+r)^α) (γ*Real.log (1+r)) (γ*r)
    simpa only [A, ← mul_sub, abs_mul] using h
  have hm : ‖C-Complex.exp (((-(γ*r):ℝ):ℂ)*Complex.I)‖ ≤
      |(1-r)^α-1| + |γ| * |Real.log (1-r)+r| := by
    have h := amplitude_phase_distance ((1-r)^α) (γ*Real.log (1-r)) (-(γ*r))
    simpa only [C, sub_neg_eq_add, ← mul_add, abs_mul] using h
  have hs := second_difference A 1 C (γ*r)
    (|(1+r)^α-1| + |γ| * |Real.log (1+r)-r|)
    (|(1-r)^α-1| + |γ| * |Real.log (1-r)+r|)
    (by simpa only [one_mul] using hp) (by simpa only [one_mul] using hm)
  norm_num only [norm_one, mul_one, one_mul] at hs
  have ha := power_amplitude_errors r α hr0 hr1 ha0 ha3
  have hl := log_phase_errors r hr0 hr1
  have hg := mul_le_mul_of_nonneg_left hl (abs_nonneg γ)
  dsimp only [A,C] at hs
  nlinarith only [hs,ha,hg]
