-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_center_proxy_moment_tail
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T09:31:15.531258+00:00
-- url     : https://prove2.me/submissions/e16a0fbe-7c99-474a-9d97-906a153ceca5

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_uniform_analytic
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastWindowTailGrowth
noncomputable def z (T t:ℝ) : ℂ := 1/4+(((T+t)/2:ℝ):ℂ)*I
noncomputable def S (v:ℂ) : ℂ :=
 (v-1/2)*Complex.log v-v+(Real.log (2*Real.pi):ℂ)/2+1/(12*v)
noncomputable def G (T t:ℝ) : ℂ :=
 Complex.Gamma (z T t)*Complex.exp (((Real.pi*(T+t)/4:ℝ):ℂ))
noncomputable def C (T t:ℝ) : ℂ :=
 Complex.exp (S (z T t)+((Real.pi*(T+t)/4:ℝ):ℂ))
noncomputable def P (T t:ℝ) : ℂ :=
 let v:=z T 0
 let u:=((t/2:ℝ):ℂ)*I
 u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
   (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)
noncomputable def delta (T t ω:ℝ) : ℂ :=
 P T t+((Real.pi*t/4:ℝ):ℂ)-I*(ω:ℂ)*t
noncomputable def carrier (t ω:ℝ) : ℂ :=
 Complex.exp (((-t^2/800:ℝ):ℂ)+I*(ω:ℂ)*t)
noncomputable def tail (T t:ℝ) : ℂ := S (z T t)-S (z T 0)-P T t

noncomputable def small (b:ℝ) : ℂ := ((-1/(4*b):ℝ):ℂ)*I
lemma log_reduction (b:ℝ) (hb:0<b) :
 Complex.log (1/4+(b:ℂ)*I)=(Real.log b:ℂ)+((Real.pi/2:ℝ):ℂ)*I+
   Complex.log (1+small b) := by
 have hn:(1+small b).re=1:=by simp only [small,add_re,one_re,mul_re,ofReal_re,ofReal_im,I_re,I_im];ring
 have hi:(1+small b).im<0 := by
  simp only [small,add_im,one_im,mul_im,ofReal_re,ofReal_im,I_re,I_im,mul_one,zero_mul,add_zero,zero_add]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

 have hne:1+small b≠0:=fun h=>by simp [h] at hn
 have ha:=abs_le.mp (Complex.abs_arg_le_pi_div_two_iff.mpr (by rw [hn];norm_num))
 have han:=Complex.arg_neg_iff.mpr hi
 have haI:Complex.arg I+Complex.arg (1+small b)∈Set.Ioc (-Real.pi) Real.pi := by
  rw [Complex.arg_I]
  constructor <;> linarith [Real.pi_pos]
 have hf:1/4+(b:ℂ)*I=(b:ℂ)*(I*(1+small b)) := by
  unfold small
  push_cast
  have hb':(b:ℂ)≠0:=by exact_mod_cast hb.ne'
  field_simp [hb']
  ring_nf
  simp only [I_sq]
  ring
 rw [hf,Complex.log_ofReal_mul hb (mul_ne_zero I_ne_zero hne),Complex.log_mul I_ne_zero hne haI,Complex.log_I]
 push_cast
 ring

lemma log_bound (b:ℝ) (hb:1500000000≤b) :
 ‖Complex.log (1/4+(b:ℂ)*I)-((Real.log b:ℂ)+((Real.pi/2:ℝ):ℂ)*I)‖≤1/10^9 := by
 have hb0:0<b:=by linarith
 have hs:‖small b‖≤1/6000000000 := by
  calc
   _ = 1/(4*b) := by
    simp only [small,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_I,mul_one,abs_div,abs_neg,abs_one,abs_mul,abs_of_pos hb0]
    norm_num
   _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

 have hs1:‖small b‖<1:=by linarith
 have hi:(1-‖small b‖)⁻¹≤2 := by
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith:0<1-‖small b‖)).mpr
  linarith
 have he:=Complex.norm_log_one_add_sub_self_le hs1
 have hp:=pow_le_pow_left₀ (norm_nonneg (small b)) hs 2
 have he':‖Complex.log (1+small b)-small b‖≤(1/6000000000:ℝ)^2 := by
  apply he.trans
  calc
   _ ≤ (1/6000000000:ℝ)^2*2/2 := div_le_div_of_nonneg_right
     (mul_le_mul hp hi (by positivity) (by positivity)) (by norm_num)
   _ = _ := by ring
 rw [log_reduction b hb0]
 have hid:(Real.log b:ℂ)+((Real.pi/2:ℝ):ℂ)*I+Complex.log (1+small b)-
   ((Real.log b:ℂ)+((Real.pi/2:ℝ):ℂ)*I)=Complex.log (1+small b):=by ring
 rw [hid]
 have hnorm:=norm_sub_le_norm_sub_add_norm_sub (Complex.log (1+small b)) (small b) 0
 simp only [sub_zero] at hnorm
 linarith

lemma scaled_polynomial_bounds (s:ℂ) (a:ℝ) (ha:1≤a) (hs:‖s‖≤(1/10000000:ℝ)*a) :
 ‖Complex.logTaylor 7 s-s‖≤(2/10^14:ℝ)*a^6 ∧
 ‖Complex.logTaylor 7 s‖≤(2/10000000:ℝ)*a^6 ∧
 ‖(∑j∈Finset.range 7,(-s)^j)-1‖≤(6/10000000:ℝ)*a^6 := by
 have ha0:0≤a:=by linarith
 have hp (j:Nat) (hj:j≤6): ‖s‖^j≤(1/10000000:ℝ)^j*a^6 := by
  calc
   _ ≤ ((1/10000000:ℝ)*a)^j := pow_le_pow_left₀ (norm_nonneg _) hs j
   _ = (1/10000000:ℝ)^j*a^j := mul_pow _ _ _
   _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha hj) (by positivity)
 have hid:Complex.logTaylor 7 s-s=
   ∑j∈Finset.range 5,(-1:ℂ)^(j+3)*s^(j+2)/((j+2:Nat):ℂ) := by
  norm_num [Complex.logTaylor,Finset.sum_range_succ]
  ring
 have hl:‖Complex.logTaylor 7 s-s‖≤(2/10^14:ℝ)*a^6 := by
  rw [hid]
  apply (norm_sum_le _ _).trans
  calc
   _ ≤ ∑j∈Finset.range 5,((1/10000000:ℝ)^(j+2)/((j+2:Nat):ℝ))*a^6 := by
    apply Finset.sum_le_sum
    intro j hj
    simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_natCast]
    have hj6:j+2≤6:=by have :=Finset.mem_range.mp hj;omega
    calc
     _ ≤ ((1/10000000:ℝ)^(j+2)*a^6)/((j+2:Nat):ℝ) := div_le_div_of_nonneg_right (hp (j+2) hj6) (by positivity)
     _ = _ := by ring
   _ ≤ _ := by
    rw [←Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    norm_num [Finset.sum_range_succ]
 have hg:‖(∑j∈Finset.range 7,(-s)^j)-1‖≤(6/10000000:ℝ)*a^6 := by
  rw [show 7=6+1 by decide,Finset.sum_range_succ']
  simp only [pow_zero,add_sub_cancel_right]
  apply (norm_sum_le _ _).trans
  calc
   _ ≤ ∑j∈Finset.range 6,(1/10000000:ℝ)^(j+1)*a^6 := by
    apply Finset.sum_le_sum
    intro j hj
    simp only [norm_pow,norm_neg]
    exact hp (j+1) (by have :=Finset.mem_range.mp hj;omega)
   _ ≤ _ := by
    rw [←Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    norm_num [Finset.sum_range_succ]
 refine ⟨hl,?_,hg⟩
 have htriangle:=norm_sub_le_norm_sub_add_norm_sub (Complex.logTaylor 7 s) s 0
 simp only [sub_zero] at htriangle
 have ha6:a≤a^6:=by simpa using pow_le_pow_right₀ ha (show 1≤6 by decide)
 have hs6:‖s‖≤(1/10000000:ℝ)*a^6:=hs.trans (mul_le_mul_of_nonneg_left ha6 (by norm_num))
 linarith

lemma delta_growth (T t a:ℝ) (hT:3000000000≤T ∧ T≤3300000000)
 (ha:1≤a) (ht:|t|≤256*a) :
 ‖delta T t (Real.log (T/2)/2-1/(48*T^2))‖≤(1/10000:ℝ)*a^7 := by
 let v:=z T 0
 let u:ℂ:=((t/2:ℝ):ℂ)*I
 let s:=u/v
 let L:=Complex.logTaylor 7 s
 let ω:=Real.log (T/2)/2-1/(48*T^2)
 have ha0:0≤a:=by linarith
 have hT0:0<T:=by linarith [hT.1]
 have hvn:(v:ℂ)≠0:=by intro h;have hi:=congrArg Complex.re h;norm_num [v,z] at hi
 have hvl:1500000000≤‖v‖ := by
  have h:=Complex.abs_im_le_norm v
  have hi:v.im=T/2:=by simp [v,z]
  rw [hi,abs_of_nonneg (by positivity:0≤T/2)] at h
  linarith [hT.1]
 have hu:‖u‖≤128*a := by
  simp only [u,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_I,mul_one,abs_div]
  norm_num
  linarith
 have hs:‖s‖≤(1/10000000:ℝ)*a := by
  change ‖u/v‖≤(1/10000000:ℝ)*a
  rw [norm_div]
  apply (div_le_iff₀ (by linarith:0<‖v‖)).mpr
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hvl)]
 have hvm:‖v-1/2‖≤2000000000 := by
  have he:v-1/2=(-1/4:ℂ)+((T/2:ℝ):ℂ)*I:=by dsimp [v,z];push_cast;ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity:0≤T/2)]
  norm_num
  linarith [hT.2]
 have hl:=scaled_polynomial_bounds s a ha hs
 have hc:‖u*(Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I))+
    I*(t:ℂ)/(48*(T:ℂ)^2)‖≤(1/10^6:ℝ)*a := by
  have hlog:‖Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I)‖≤1/10^9:=by
   simpa only [v,z,add_zero] using log_bound (T/2) (by linarith [hT.1])
  have hd:‖I*(t:ℂ)/(48*(T:ℂ)^2)‖≤(1/10^9:ℝ)*a := by
   have he:‖I*(t:ℂ)/(48*(T:ℂ)^2)‖=|t|/(48*T^2) := by
    rw [norm_div,norm_mul,norm_mul,norm_pow,norm_I,Complex.norm_real,Real.norm_eq_abs]
    norm_num
   rw [he]
   apply (div_le_iff₀ (by positivity:0<48*T^2)).mpr
   have hbig:(3000000000:ℝ)^2≤T^2:=pow_le_pow_left₀ (by norm_num) hT.1 2
   nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hbig)]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hp:=mul_le_mul hu hlog (norm_nonneg _) (by positivity)
  linarith

 have hid:delta T t ω=
   (u*(Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I))+
      I*(t:ℂ)/(48*(T:ℂ)^2))+
   (v-1/2)*(L-s)+u*L-u/(2*v)+(1/(12*v))*((∑j∈Finset.range 7,(-s)^j)-1) := by
  change u*(Complex.log v-1)+(v+u-1/2)*L+
    (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)+((Real.pi*t/4:ℝ):ℂ)-I*(ω:ℂ)*t=_
  have hTn:(T:ℂ)≠0:=by exact_mod_cast hT0.ne'
  dsimp [ω,s,u]
  simp only [neg_div]
  push_cast
  field_simp [hvn,hTn]
  ring_nf
  simp only [I_sq]
  ring


 rw [hid]
 have ha17:a≤a^7:=by simpa using pow_le_pow_right₀ ha (show 1≤7 by decide)
 have ha67:a^6≤a^7:=pow_le_pow_right₀ ha (by decide)
 have hc7:‖u*(Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I))+
    I*(t:ℂ)/(48*(T:ℂ)^2)‖≤(1/10^6:ℝ)*a^7 :=
  hc.trans (mul_le_mul_of_nonneg_left ha17 (by norm_num))
 have h1:‖(v-1/2)*(L-s)‖≤(4/100000:ℝ)*a^7 := by
  rw [norm_mul]
  apply (mul_le_mul hvm hl.1 (norm_nonneg _) (by norm_num)).trans
  nlinarith
 have h2:‖u*L‖≤(256/10000000:ℝ)*a^7 := by
  rw [norm_mul]
  convert! mul_le_mul hu hl.2.1 (norm_nonneg _) (by positivity) using 1 <;> ring
 have h3:‖u/(2*v)‖≤(1/10000000:ℝ)*a^7 := by
  have h3a:‖u/(2*v)‖≤(1/10000000:ℝ)*a := by
   rw [norm_div]
   have hd:‖(2:ℂ)*v‖=2*‖v‖:=by rw [norm_mul];norm_num
   rw [hd]
   apply (div_le_iff₀ (by linarith:0<2*‖v‖)).mpr
   nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hvl)]
  exact h3a.trans (mul_le_mul_of_nonneg_left ha17 (by norm_num))
 have h4:‖(1/(12*v))*((∑j∈Finset.range 7,(-s)^j)-1)‖≤(1/10^12:ℝ)*a^7 := by
  rw [norm_mul,norm_div,norm_one,norm_mul,norm_ofNat]
  have hi:(1:ℝ)/(12*‖v‖)≤1/(12*1500000000) :=
   div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  apply (mul_le_mul hi hl.2.2 (norm_nonneg _) (by norm_num)).trans
  nlinarith [pow_nonneg ha0 6]
 have hab:=norm_add_le
   (u*(Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I))+I*(t:ℂ)/(48*(T:ℂ)^2)) ((v-1/2)*(L-s))
 have habc:=norm_add_le
   ((u*(Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I))+I*(t:ℂ)/(48*(T:ℂ)^2))+(v-1/2)*(L-s)) (u*L)
 have habcd:=norm_sub_le
   (((u*(Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I))+I*(t:ℂ)/(48*(T:ℂ)^2))+(v-1/2)*(L-s))+u*L) (u/(2*v))
 have hlast:=norm_add_le
   ((((u*(Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I))+I*(t:ℂ)/(48*(T:ℂ)^2))+(v-1/2)*(L-s))+u*L)-u/(2*v))
   ((1/(12*v))*((∑j∈Finset.range 7,(-s)^j)-1))
 linarith
end RHFastWindowTailGrowth

namespace RHFastWindowTailKernel
noncomputable def expPolynomial (d:ℂ) : ℂ := ∑r∈Finset.range 5,d^r/(r.factorial:ℂ)
noncomputable def factor (k:Nat) (t:ℝ) : ℂ :=
 (-2*(Real.pi:ℂ)*I*(t:ℂ))^k/((k.factorial:ℂ)*(512:ℂ)^k)
lemma expPolynomial_bound (d:ℂ) (a:ℝ) (ha:1≤a) (hd:‖d‖≤(1/10000:ℝ)*a^7) :
 ‖expPolynomial d‖≤5*a^28 := by
 have ha0:0≤a:=by linarith
 have hd':‖d‖≤a^7:=by nlinarith [pow_nonneg ha0 7]
 unfold expPolynomial
 apply (norm_sum_le _ _).trans
 calc
  _ ≤ ∑r∈Finset.range 5,a^28 := by
   apply Finset.sum_le_sum
   intro r hr
   have hr4:r≤4:=by have :=Finset.mem_range.mp hr;omega
   have hf:1≤(r.factorial:ℝ):=by exact_mod_cast (show 1≤r.factorial from Nat.factorial_pos r)
   simp only [norm_div,norm_pow,Complex.norm_natCast]
   apply (div_le_iff₀ (by positivity:(0:ℝ)<r.factorial)).mpr
   have hp:‖d‖^r≤a^28 := by
    calc
     _ ≤ (a^7)^r:=pow_le_pow_left₀ (norm_nonneg _) hd' r
     _ = a^(7*r):=(pow_mul _ _ _).symm
     _ ≤ _:=pow_le_pow_right₀ ha (by omega)
   nlinarith [pow_nonneg ha0 28]
  _ = _ := by norm_num
lemma factor_norm (k:Nat) (t:ℝ) : ‖factor k t‖≤Real.exp (|t|/64) := by
 have hd:(0:ℝ)<(k.factorial:ℝ)*(512:ℝ)^k:=by positivity
 have hn:‖-2*(Real.pi:ℂ)*I*(t:ℂ)‖=2*Real.pi*|t|:=by
  rw [norm_mul,norm_mul,norm_mul,norm_neg]
  norm_num [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
 have he:(2*Real.pi*|t|)^k/((k.factorial:ℝ)*512^k)=
   (Real.pi*|t|/256)^k/(k.factorial:ℝ) := by
  rw [div_pow]
  field_simp
  rw [show (512:ℝ)^k=(2:ℝ)^k*256^k by rw [←mul_pow];norm_num]
  ring
 simp only [factor,norm_div,norm_pow,norm_mul,Complex.norm_natCast,norm_ofNat,hn]
 rw [he]
 have hp:=Real.pow_div_factorial_le_exp (Real.pi*|t|/256) (by positivity) k
 apply hp.trans
 apply Real.exp_le_exp.mpr
 nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr Real.pi_lt_four.le)]
lemma gaussian_tail (t:ℝ) (ht:256≤|t|) :
 (|t|/256)^28*Real.exp (|t|/64-t^2/800)≤Real.exp (-|t|/4) := by
 have ha:0≤|t|/256:=by positivity
 have he:|t|/256≤Real.exp (|t|/256-1):=by
  have h:=Real.add_one_le_exp (|t|/256-1)
  linarith
 have hp:=pow_le_pow_left₀ ha he 28
 have hp':(|t|/256)^28≤Real.exp (28*(|t|/256-1)) := by
  convert! hp using 1
  rw [←Real.exp_nat_mul]
  norm_num
 calc
  _ ≤ Real.exp (28*(|t|/256-1))*Real.exp (|t|/64-t^2/800) :=
   mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le
  _ = Real.exp (28*(|t|/256-1)+(|t|/64-t^2/800)):=by rw [Real.exp_add]
  _ ≤ _ := by
   apply Real.exp_le_exp.mpr
   nlinarith [sq_abs t,sq_nonneg (|t|-256)]
lemma proxy_moment_tail (A d:ℂ) (ω t:ℝ) (k:Nat)
 (hA:‖A‖≤7) (ht:256≤|t|) (hd:‖d‖≤(1/10000:ℝ)*(|t|/256)^7) :
 ‖A*Complex.exp (((-t^2/800:ℝ):ℂ)+I*(ω:ℂ)*t)*expPolynomial d*factor k t‖≤
   35*Real.exp (-|t|/4) := by
 have ha:1≤|t|/256:=by linarith
 have hq:=expPolynomial_bound d (|t|/256) ha hd
 have hf:=factor_norm k t
 have hc:‖Complex.exp (((-t^2/800:ℝ):ℂ)+I*(ω:ℂ)*t)‖=Real.exp (-t^2/800):=by
  rw [Complex.norm_exp]
  congr 1
  simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im]
  ring
 rw [norm_mul,norm_mul,norm_mul,hc]
 calc
  _ ≤ 7*Real.exp (-t^2/800)*(5*(|t|/256)^28)*Real.exp (|t|/64):=by gcongr
  _ = 35*((|t|/256)^28*Real.exp (|t|/64-t^2/800)):=by
   rw [sub_eq_add_neg,Real.exp_add]
   ring
  _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_tail t ht) (by norm_num)
end RHFastWindowTailKernel


namespace RHFastActualProxyTail
open RHFastGaussianWindow
lemma anchor_bound (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) :
 ‖anchor T‖≤7 := by
 have h:‖Complex.Gamma (center T)*Complex.exp (((Real.pi*(T:ℝ)/4:ℝ):ℂ))-anchor T‖≤1/10^25 := by
  have h:=TaoFivePrimes.rh_fast_kernel_gamma_uniform_analytic T 8192 hT (by omega) (by decide)
  dsimp only at h
  norm_num only [Nat.cast_ofNat,Int.cast_ofNat] at h
  have hb:(((T:Int)*32).toNat)=T*32 := by omega
  simp only [add_zero,sub_zero,hb] at h
  change ‖_-anchor T‖≤_ at h
  convert! h using 1 <;> (try congr 3) <;> (try congr 1) <;> ((try dsimp only [center]);push_cast;ring)
 have hg:=TaoFivePrimes.rh_high_height_scaled_gamma_bound.1 ((T:ℝ)/2)
 have hgn:‖Complex.Gamma (center T)*Complex.exp (((Real.pi*(T:ℝ)/4:ℝ):ℂ))‖≤6 := by
  rw [norm_mul,Complex.norm_exp]
  simp only [ofReal_re]
  convert! hg using 1 <;> (try rfl) <;> (congr 2 <;> ((try dsimp only [center]);push_cast;ring))
 have htriangle:=norm_sub_le_norm_sub_add_norm_sub (anchor T)
  (Complex.Gamma (center T)*Complex.exp (((Real.pi*(T:ℝ)/4:ℝ):ℂ))) 0
 simp only [sub_zero] at htriangle
 rw [norm_sub_rev (anchor T) (Complex.Gamma (center T)*Complex.exp (((Real.pi*(T:ℝ)/4:ℝ):ℂ)))] at htriangle
 linarith
lemma actual_tail (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (t:ℝ)
 (ht:256≤|t|) : ‖momentProxy T k t‖≤35*Real.exp (-|t|/4) := by
 have hTr:3000000000≤(T:ℝ) ∧ (T:ℝ)≤3300000000:=by
  constructor
  · exact_mod_cast (show 3000000000≤T by omega)
  · exact_mod_cast hU
 have hd:=RHFastWindowTailGrowth.delta_growth (T:ℝ) t (|t|/256) hTr
  (by linarith) (by linarith)
 have hd':‖delta T t‖≤(1/10000:ℝ)*(|t|/256)^7:=by
  simpa only [delta,center,omega,RHFastWindowTailGrowth.delta,
   RHFastWindowTailGrowth.P,RHFastWindowTailGrowth.z,add_zero] using hd
 have h:=RHFastWindowTailKernel.proxy_moment_tail (anchor T) (delta T t) (omega T) t k
  (anchor_bound T hT hU) ht hd'
 simpa only [momentProxy,proxy,carrier,exponentialPolynomial,momentFactor,
   RHFastWindowTailKernel.expPolynomial,RHFastWindowTailKernel.factor] using h
end RHFastActualProxyTail

theorem solution (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (t:ℝ)
 (ht:256≤|t|) : ‖RHFastGaussianWindow.momentProxy T k t‖≤35*Real.exp (-|t|/4) :=
 RHFastActualProxyTail.actual_tail T hT hU k t ht
#print axioms solution
