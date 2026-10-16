-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_center_stirling_increment
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:55:02.131949+00:00
-- url     : https://prove2.me/submissions/d60523d9-d364-444a-ae38-77440c3adeae

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastCenterStirling
noncomputable def exponent (z:ℂ) : ℂ := (z-1/2)*Complex.log z-z+1/(12*z)
noncomputable def increment (z u:ℂ) : ℂ :=
  u*(Complex.log z-1)+(z+u-1/2)*Complex.logTaylor 7 (u/z)+
    (1/(12*z))*((∑j∈Finset.range 7,(-u/z)^j)-1)

lemma log_increment (z u:ℂ) (hz:0<z.re) (hr:‖u/z‖<1) :
  Complex.log (z+u)=Complex.log z+Complex.log (1+u/z) := by
  have hn:z≠0:=fun h=>by simp [h] at hz
  have hq:0<(1+u/z).re := by
    have ha:=Complex.abs_re_le_norm (u/z)
    have hb:-(‖u/z‖)≤(u/z).re := (abs_le.mp ha).1
    simp only [add_re,one_re]
    linarith
  have hqn:1+u/z≠0:=fun h=>by simp [h] at hq
  have haz:=abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have haq:=abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hq))
  have harg:Complex.arg z+Complex.arg (1+u/z)∈Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith
  have he:z+u=z*(1+u/z):=by field_simp [hn] <;> ring
  rw [he,Complex.log_mul hn hqn harg]

lemma reciprocal_remainder (z u:ℂ) (hz:z≠0) (hu:z+u≠0) :
  1/(z+u)-(1/z)*(∑j∈Finset.range 7,(-u/z)^j)=(-u/z)^7/(z+u) := by
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,zero_add]
  field_simp [hz,hu]
  ring

lemma error_identity (z u:ℂ) (hz:0<z.re) (hr:‖u/z‖<1) :
  exponent (z+u)-exponent z-increment z u=
    (z+u-1/2)*(Complex.log (1+u/z)-Complex.logTaylor 7 (u/z))+
    (1/12:ℂ)*(-u/z)^7/(z+u) := by
  have hn:z≠0:=fun h=>by simp [h] at hz
  have hq:1+u/z≠0 := by
    intro he
    have ht:u/z= -1 := by linear_combination he
    rw [ht] at hr
    norm_num at hr
  have hu:z+u≠0 := by
    have he:z+u=z*(1+u/z):=by field_simp [hn] <;> ring
    rw [he]
    exact mul_ne_zero hn hq
  have hg:=reciprocal_remainder z u hn hu
  unfold exponent increment
  rw [log_increment z u hz hr]
  simp only [div_eq_mul_inv,mul_inv_rev] at hg ⊢
  linear_combination (1/12:ℂ)*hg

lemma error_bound (z u:ℂ) (hz:0<z.re) (hr:‖u/z‖≤1/10000000)
    (hs:‖z+u-1/2‖≤3000000000) (hl:1000000000≤‖z+u‖) :
  ‖exponent (z+u)-exponent z-increment z u‖≤1/10^38 := by
  have hr1:‖u/z‖<1:=by linarith
  have hlog:=Complex.norm_log_sub_logTaylor_le 6 hr1
  have hi:(1-‖u/z‖)⁻¹≤2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith:0<1-‖u/z‖)).mpr
    linarith
  have hp:‖u/z‖^7≤(1/10000000:ℝ)^7:=pow_le_pow_left₀ (norm_nonneg _) hr _
  have hlog':‖Complex.log (1+u/z)-Complex.logTaylor 7 (u/z)‖≤
      (1/10000000:ℝ)^7*2/7 := by
    calc
      _ ≤ ‖u/z‖^7*(1-‖u/z‖)⁻¹/7 := by convert hlog using 1 <;> norm_num
      _ ≤ (1/10000000:ℝ)^7*2/7 := div_le_div_of_nonneg_right
        (mul_le_mul hp hi (by positivity) (by positivity)) (by norm_num)

  rw [error_identity z u hz hr1]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_div,norm_mul,norm_div,norm_pow]
  have hn:‖(-u)/z‖=‖u/z‖:=by rw [neg_div,norm_neg]
  rw [hn]
  norm_num only [norm_one,norm_ofNat]
  have hdiv:(1/12:ℝ)*‖u/z‖^7/‖z+u‖≤(1/12:ℝ)*(1/10000000:ℝ)^7/1000000000 := by
    calc
      _ ≤ (1/12:ℝ)*(1/10000000:ℝ)^7/‖z+u‖ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by norm_num)) (norm_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num) hl
  calc
    _ ≤ (3000000000:ℝ)*((1/10000000:ℝ)^7*2/7)+
        (1/12:ℝ)*(1/10000000:ℝ)^7/1000000000 :=
      add_le_add (mul_le_mul hs hlog' (norm_nonneg _) (by norm_num)) hdiv
    _ ≤ _ := by norm_num

end RHFastCenterStirling

theorem solution (z u:ℂ) (hz:0<z.re) (hr:‖u/z‖≤1/10000000)
    (hs:‖z+u-1/2‖≤3000000000) (hl:1000000000≤‖z+u‖) :
  ‖((z+u-1/2)*Complex.log (z+u)-(z+u)+1/(12*(z+u)))-
    ((z-1/2)*Complex.log z-z+1/(12*z))-
    (u*(Complex.log z-1)+(z+u-1/2)*Complex.logTaylor 7 (u/z)+
      (1/(12*z))*((∑j∈Finset.range 7,(-u/z)^j)-1))‖≤1/10^38 :=
  RHFastCenterStirling.error_bound z u hz hr hs hl
#print axioms solution
