-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_oscillatory_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:24:53.946271+00:00
-- url     : https://prove2.me/submissions/270711d2-ef45-4d51-a5fd-e4ff7f26ad93

import Theorems.Thm_TaoFivePrimes_sine_squared_interval_enclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex Finset Metric

namespace DirectOscillatoryBound

private lemma cos_lower (x : ℝ) (hx : |x| ≤ (11/10:ℝ)) : (9/20:ℝ) ≤ Real.cos x := by
  have hs := TaoFivePrimes.sine_squared_interval_enclosure (11/20) (11/20) (11/20) (11/20) 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsin : (Real.sin (11/20:ℝ))^2 ≤ (11/20-(11/20:ℝ)^3/6+(11/20:ℝ)^5/100)^2 := by
    simpa using hs
  have hid := Real.sin_sq_eq_half_sub (11/20:ℝ)
  have hc : (9/20:ℝ) ≤ Real.cos (11/10) := by
    norm_num at hid
    nlinarith [hsin]
  have hp : (11/10:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (x:=|x|) (y:=(11/10:ℝ)) (abs_nonneg x) hp hx
  rw [Real.cos_abs] at hm
  linarith

private lemma theta_term_bound (n : ℕ) (z : ℂ) (hi : |z.im| ≤ (11/10:ℝ)) :
    ‖Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)‖ ≤
      Real.exp (-(7/5)*Real.exp z.re) := by
  have hc := cos_lower z.im hi
  have hn : (1:ℝ) ≤ (n+1:ℝ)^2 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
  have hp : (7/5:ℝ) ≤ Real.pi*(n+1:ℝ)^2*Real.cos z.im := by
    have h1 : (157/50:ℝ) ≤ Real.pi*(n+1:ℝ)^2 :=
      (by linarith [Real.pi_gt_d2] : (157/50:ℝ) ≤ Real.pi).trans
        (le_mul_of_one_le_right Real.pi_pos.le hn)
    have hm := mul_le_mul h1 hc (by norm_num : (0:ℝ) ≤ 9/20)
      (by positivity : (0:ℝ) ≤ Real.pi*(n+1:ℝ)^2)
    linarith
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [mul_re,neg_re,ofReal_re,neg_im,ofReal_im,neg_zero,mul_im,
    natCast_re,natCast_im,add_re,one_re,add_im,one_im,pow_two,Complex.exp_re,Complex.exp_im]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) (Real.exp_pos z.re).le]


noncomputable def theta (z : ℂ) : ℂ :=
  ∑ n ∈ range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

noncomputable def kernel (τ : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4)*(z^k/(k.factorial:ℂ))*Complex.exp (Complex.I*(τ:ℂ)*z)*theta z

lemma kernel_bound (τ : ℝ) (hτ : |τ| ≤ 100) (k : ℕ) (c : ℝ)
    (hc0 : 0≤c) (hc1 : c≤6) (z : ℂ) (hz : ‖z-(c:ℂ)‖ ≤ (11/10:ℝ)) :
    ‖kernel τ k z‖ ≤ 10^59 := by
  have hre : |z.re-c| ≤ (11/10:ℝ) := by
    simpa only [sub_re,ofReal_re] using (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
  have him : |z.im| ≤ (11/10:ℝ) := by
    simpa only [sub_im,ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(c:ℂ))).trans hz
  have hr : -(11/10:ℝ) ≤ z.re := by linarith [(abs_le.mp hre).1]
  have hn : ‖z‖ ≤ (71/10:ℝ) := by
    have h := norm_add_le (z-(c:ℂ)) (c:ℂ)
    rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0] at h
    linarith
  have hp : ‖z^k/(k.factorial:ℂ)‖ ≤ Real.exp (71/10) := by
    have h := Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg _) k
    have h' : ‖z^k/(k.factorial:ℂ)‖ ≤ Real.exp ‖z‖ := by
      simpa [norm_div,norm_pow] using h
    exact h'.trans (Real.exp_le_exp.mpr hn)
  have hphase : ‖Complex.exp (Complex.I*(τ:ℂ)*z)‖ ≤ Real.exp 110 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul hτ him (abs_nonneg z.im) (by norm_num : (0:ℝ) ≤ 100)
    have he : |τ*z.im| ≤ (110:ℝ) := by
      rw [abs_mul]
      nlinarith
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,zero_add,add_zero,zero_sub]
    linarith [neg_le_abs (τ*z.im)]
  have ht : ‖theta z‖ ≤ 8*Real.exp (-(7/5)*Real.exp z.re) := by
    unfold theta
    calc
      _ ≤ ∑ n ∈ range 8, ‖Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range 8, Real.exp (-(7/5)*Real.exp z.re) :=
        sum_le_sum (fun n _ => theta_term_bound n z him)
      _ = _ := by simp
  have he : z.re/4-(7/5)*Real.exp z.re ≤ 0 := by
    have h := Real.add_one_le_exp z.re
    linarith
  unfold kernel
  simp only [norm_mul]
  rw [show ‖(2:ℂ)‖=2 by norm_num]
  calc
    _ ≤ 2*Real.exp (z.re/4)*Real.exp (71/10)*Real.exp 110*
        (8*Real.exp (-(7/5)*Real.exp z.re)) := by
      gcongr
      rw [Complex.norm_exp]
      simp
    _ = 16*Real.exp (z.re/4-(7/5)*Real.exp z.re)*Real.exp (71/10)*Real.exp 110 := by
      rw [show z.re/4-(7/5)*Real.exp z.re = z.re/4+(-(7/5)*Real.exp z.re) by ring,Real.exp_add]
      ring
    _ ≤ 16*Real.exp (71/10)*Real.exp 110 := by
      have hh : Real.exp (z.re/4-(7/5)*Real.exp z.re) ≤ 1 := by
        simpa using Real.exp_le_exp.mpr he
      have h1 := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 16)
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (71/10)).le
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos 110).le
      simpa using h3
    _ = 16*Real.exp ((71/10)+110) := by rw [Real.exp_add]; ring
    _ ≤ 16*Real.exp 118 := by gcongr; norm_num
    _ ≤ 16*(3:ℝ)^118 := by
      rw [show Real.exp 118=(Real.exp 1)^118 by
        simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 118]
      gcongr
      linarith [Real.exp_one_lt_d9]
    _ ≤ 10^59 := by norm_num

end DirectOscillatoryBound

theorem solution (τ : ℝ) (hτ : |τ| ≤ 100) (k : ℕ) (c : ℝ)
    (hc0 : 0≤c) (hc1 : c≤6) (z : ℂ) (hz : ‖z-(c:ℂ)‖ ≤ (11/10:ℝ)) :
    ‖2*Complex.exp (z/4)*(z^k/(k.factorial:ℂ))*Complex.exp (Complex.I*(τ:ℂ)*z)*
      (∑ n ∈ Finset.range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z))‖ ≤ 10^59 := by
  simpa [DirectOscillatoryBound.kernel,DirectOscillatoryBound.theta] using
    DirectOscillatoryBound.kernel_bound τ hτ k c hc0 hc1 z hz
