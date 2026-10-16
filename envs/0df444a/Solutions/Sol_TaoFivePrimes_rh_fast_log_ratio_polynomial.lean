-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_log_ratio_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:00:05.983186+00:00
-- url     : https://prove2.me/submissions/7c9b0d3c-85dc-463e-a9bf-8936b3a864c1

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex Finset
namespace RHFastLogRatioPolynomial
lemma odd_identity (z:ℂ) :
 Complex.logTaylor 129 z-Complex.logTaylor 129 (-z)=
  2*z*(∑k∈Finset.range 64,z^(2*k)/((2*k+1:Nat):ℂ)) := by
 norm_num [Complex.logTaylor,Finset.sum_range_succ]
 ring
lemma remainder (z:ℂ) (hz:‖z‖≤1/3) :
 ‖Complex.log (1+z)-Complex.logTaylor 129 z‖≤(1/3:ℝ)^129*2/129 := by
 have hz1:‖z‖<1:=by linarith
 have h:=Complex.norm_log_sub_logTaylor_le 128 hz1
 have hp:=pow_le_pow_left₀ (norm_nonneg z) hz 129
 have hi:(1-‖z‖)⁻¹≤2:=by
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith:0<1-‖z‖)).mpr
  linarith
 calc
  _ ≤ ‖z‖^129*(1-‖z‖)⁻¹/129 := by convert! h using 1 <;> norm_num
  _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul hp hi (by positivity) (by positivity)) (by norm_num)
lemma approximation (x:ℝ) (hx0:0≤x) (hx:x≤1/3) :
 ‖((Real.log ((1+x)/(1-x)):ℝ):ℂ)-
   2*(x:ℂ)*(∑k∈Finset.range 64,(x:ℂ)^(2*k)/((2*k+1:Nat):ℂ))‖≤1/(2:ℝ)^128 := by
 have hplus:0<1+x:=by linarith
 have hminus:0<1-x:=by linarith
 have hz:‖(x:ℂ)‖≤1/3:=by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx0] using hx
 have hlog:((Real.log ((1+x)/(1-x)):ℝ):ℂ)=Complex.log (1+(x:ℂ))-Complex.log (1-(x:ℂ)) := by
  rw [Real.log_div hplus.ne' hminus.ne',Complex.ofReal_sub,Complex.ofReal_log hplus.le,Complex.ofReal_log hminus.le]
  simp only [Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_one]
 rw [hlog,←odd_identity]
 have hid:(Complex.log (1+(x:ℂ))-Complex.log (1-(x:ℂ)))-
   (Complex.logTaylor 129 (x:ℂ)-Complex.logTaylor 129 (-(x:ℂ)))=
   (Complex.log (1+(x:ℂ))-Complex.logTaylor 129 (x:ℂ))-
   (Complex.log (1-(x:ℂ))-Complex.logTaylor 129 (-(x:ℂ))) := by ring
 rw [hid]
 apply (norm_sub_le _ _).trans
 have hp:=remainder (x:ℂ) hz
 have hm:=remainder (-(x:ℂ)) (by simpa only [norm_neg] using hz)
 have hm':‖Complex.log (1-(x:ℂ))-Complex.logTaylor 129 (-(x:ℂ))‖≤(1/3:ℝ)^129*2/129:=by
  simpa only [sub_eq_add_neg] using hm
 apply (add_le_add hp hm').trans
 norm_num
end RHFastLogRatioPolynomial

theorem solution (x:ℝ) (hx0:0≤x) (hx:x≤1/3) :
 ‖((Real.log ((1+x)/(1-x)):ℝ):ℂ)-
   2*(x:ℂ)*(∑k∈Finset.range 64,(x:ℂ)^(2*k)/((2*k+1:Nat):ℂ))‖≤1/(2:ℝ)^128 :=
 RHFastLogRatioPolynomial.approximation x hx0 hx
#print axioms solution
