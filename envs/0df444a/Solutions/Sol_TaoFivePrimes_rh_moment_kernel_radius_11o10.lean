-- Prove2me | solution 1 for TaoFivePrimes.rh_moment_kernel_radius_11o10
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:04:12.905166+00:00
-- url     : https://prove2.me/submissions/2e5e10dd-2f9c-4f99-98a9-da0b1d3c9774

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

namespace MomentRadius11o10

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

private lemma exp_three_bound : (2007/100:ℝ) ≤ Real.exp 3 := by
  have hbase : (2718/1000:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000) hbase 3
  have he : Real.exp 3=(Real.exp 1)^3 := by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 3
  rw [he]
  norm_num at hp ⊢
  linarith

private lemma log_twentyfive : Real.log 25 ≤ (161/50:ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<25)).mpr
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 11/50) 8
  norm_num [Finset.sum_range_succ] at hs
  have hm := mul_le_mul exp_three_bound hs (by norm_num) (Real.exp_pos 3).le
  have he : Real.exp (161/50)=Real.exp 3*Real.exp (11/50) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith

private lemma log_fortysix : Real.log 46 ≤ (383/100:ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<46)).mpr
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 83/100) 8
  norm_num [Finset.sum_range_succ] at hs
  have hm := mul_le_mul exp_three_bound hs (by norm_num) (Real.exp_pos 3).le
  have he : Real.exp (383/100)=Real.exp 3*Real.exp (83/100) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith

private lemma exp_tangent_20 (r : ℝ) (hr : 2≤r) : (20:ℝ)*r-40 ≤ Real.exp r := by
  have he := Real.add_one_le_exp (r-3)
  have hmul := mul_le_mul (by linarith [exp_three_bound] : (20:ℝ)≤Real.exp 3) he
    (by linarith) (Real.exp_pos 3).le
  have hx : Real.exp 3*Real.exp (r-3)=Real.exp r := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hx] at hmul
  linarith

private lemma exp_tangent_25 (r : ℝ) : (25:ℝ)*r-111/2 ≤ Real.exp r := by
  have he := Real.add_one_le_exp (r-Real.log 25)
  rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<25)] at he
  nlinarith [log_twentyfive]

private lemma exp_tangent_46 (r : ℝ) : (46:ℝ)*r-6509/50 ≤ Real.exp r := by
  have he := Real.add_one_le_exp (r-Real.log 46)
  rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<46)] at he
  nlinarith [log_fortysix]

noncomputable def theta (z : ℂ) : ℂ :=
  ∑ n ∈ range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)

noncomputable def kernel (k : ℕ) (z : ℂ) : ℂ :=
  2*Complex.exp (z/4)*((64*z)^k/(k.factorial:ℂ))*theta z

lemma kernel_bound (k : ℕ) (c : ℝ) (hc : 0≤c) (z : ℂ)
    (hz : ‖z-(c:ℂ)‖ ≤ (11/10:ℝ)) : ‖kernel k z‖ ≤ 11*10^84 := by
  have hre : |z.re-c| ≤ (11/10:ℝ) := by
    simpa only [sub_re,ofReal_re] using (Complex.abs_re_le_norm (z-(c:ℂ))).trans hz
  have him : |z.im| ≤ (11/10:ℝ) := by
    simpa only [sub_im,ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(c:ℂ))).trans hz
  have hr : -(11/10:ℝ) ≤ z.re := by linarith [(abs_le.mp hre).1]
  have himsq : z.im^2 ≤ (121/100:ℝ) := by
    have hi := abs_le.mp him
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hi.1)]
  have hp : ‖(64*z)^k/(k.factorial:ℂ)‖ ≤ Real.exp (64*‖z‖) := by
    simpa [norm_div,norm_pow,norm_mul] using
      Real.pow_div_factorial_le_exp (64*‖z‖) (by positivity) k
  have ht : ‖theta z‖ ≤ 8*Real.exp (-(7/5)*Real.exp z.re) := by
    unfold theta
    calc
      _ ≤ ∑ n ∈ range 8, ‖Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range 8, Real.exp (-(7/5)*Real.exp z.re) :=
        sum_le_sum (fun n _ => theta_term_bound n z him)
      _ = _ := by simp
  have he : z.re/4+64*‖z‖-(7/5)*Real.exp z.re ≤ 193 := by
    by_cases h35 : (7/2:ℝ) ≤ z.re
    · have hnorm : ‖z‖ ≤ z.re+173/1000 := by
        have hs := Complex.sq_norm_sub_sq_re z
        apply (sq_le_sq₀ (norm_nonneg z) (by linarith : 0≤z.re+173/1000)).mp
        nlinarith
      have ht := exp_tangent_46 z.re
      linarith
    · by_cases h3 : (3:ℝ) ≤ z.re
      · have hnorm : ‖z‖ ≤ z.re+197/1000 := by
          have hs := Complex.sq_norm_sub_sq_re z
          apply (sq_le_sq₀ (norm_nonneg z) (by linarith : 0≤z.re+197/1000)).mp
          nlinarith
        have ht := exp_tangent_25 z.re
        linarith
      · by_cases h25 : (5/2:ℝ) ≤ z.re
        · have hnorm : ‖z‖ ≤ z.re+1/4 := by
            have hs := Complex.sq_norm_sub_sq_re z
            apply (sq_le_sq₀ (norm_nonneg z) (by linarith : 0≤z.re+1/4)).mp
            nlinarith
          have ht := exp_tangent_20 z.re (by linarith)
          linarith
        · have hrsq : z.re^2 ≤ (25/4:ℝ) := by
            nlinarith [mul_nonneg (by linarith : 0≤5/2-z.re) (by linarith : 0≤5/2+z.re)]
          have hnorm : ‖z‖ ≤ (11/4:ℝ) := by
            have hs := Complex.sq_norm_sub_sq_re z
            apply (sq_le_sq₀ (norm_nonneg z) (by norm_num : (0:ℝ)≤11/4)).mp
            nlinarith
          have hx := Real.exp_pos z.re
          linarith
  unfold kernel
  simp only [norm_mul]
  rw [show ‖(2:ℂ)‖=2 by norm_num]
  calc
    _ ≤ 2*Real.exp (z.re/4)*Real.exp (64*‖z‖)*(8*Real.exp (-(7/5)*Real.exp z.re)) := by
      gcongr
      rw [Complex.norm_exp]
      simp
    _ = 16*Real.exp (z.re/4+64*‖z‖-(7/5)*Real.exp z.re) := by
      rw [show z.re/4+64*‖z‖-(7/5)*Real.exp z.re =
        z.re/4+64*‖z‖+(-(7/5)*Real.exp z.re) by ring,Real.exp_add,Real.exp_add]
      ring
    _ ≤ 16*Real.exp 193 := by gcongr
    _ ≤ 16*(27183/10000:ℝ)^193 := by
      rw [show Real.exp 193=(Real.exp 1)^193 by
        simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 193]
      gcongr
      linarith [Real.exp_one_lt_d9]
    _ ≤ 11*10^84 := by norm_num

end MomentRadius11o10

theorem solution (k : ℕ) (c : ℝ) (hc : 0≤c) (z : ℂ)
    (hz : ‖z-(c:ℂ)‖ ≤ (11/10:ℝ)) :
    ‖2*Complex.exp (z/4)*((64*z)^k/(k.factorial:ℂ))*
      (∑ n ∈ Finset.range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z))‖ ≤ 11*10^84 := by
  simpa [MomentRadius11o10.kernel,MomentRadius11o10.theta] using
    MomentRadius11o10.kernel_bound k c hc z hz
