-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_center_gamma_polynomial_uniform
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T23:14:30.301083+00:00
-- url     : https://prove2.me/submissions/b3114076-8dfa-496b-960e-57919f4255ef

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_fast_center_stirling_increment
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_uniform_analytic
import Theorems.Thm_TaoFivePrimes_rh_high_height_complex_stirling
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastUniformGammaPolynomialProofGuard
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

lemma log_poly_bounds (s:ℂ) (hs:‖s‖≤1/10000000) :
 ‖Complex.logTaylor 7 s-s‖≤2/10^14 ∧ ‖Complex.logTaylor 7 s‖≤2/10000000 := by
 have hs1:‖s‖<1:=by linarith
 have hi:(1-‖s‖)⁻¹≤2 := by
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith:0<1-‖s‖)).mpr
  linarith
 have hlog:=Complex.norm_log_one_add_sub_self_le hs1
 have hrem:=Complex.norm_log_sub_logTaylor_le 6 hs1
 have hp2:=pow_le_pow_left₀ (norm_nonneg s) hs 2
 have hp7:=pow_le_pow_left₀ (norm_nonneg s) hs 7
 have he1:‖Complex.log (1+s)-s‖≤1/10^14 := by
  apply hlog.trans
  calc
   _ ≤ (1/10000000:ℝ)^2*2/2 := div_le_div_of_nonneg_right
    (mul_le_mul hp2 hi (by positivity) (by positivity)) (by norm_num)
   _ = _ := by norm_num
 have he2:‖Complex.log (1+s)-Complex.logTaylor 7 s‖≤1/10^14 := by
  calc
   _ ≤ ‖s‖^7*(1-‖s‖)⁻¹/7 := by convert hrem using 1 <;> norm_num
   _ ≤ (1/10000000:ℝ)^7*2/7 := div_le_div_of_nonneg_right
    (mul_le_mul hp7 hi (by positivity) (by positivity)) (by norm_num)
   _ ≤ _ := by norm_num
 have he:‖Complex.logTaylor 7 s-s‖≤2/10^14 := by
  have h:=norm_sub_le_norm_sub_add_norm_sub (Complex.logTaylor 7 s) (Complex.log (1+s)) s
  rw [norm_sub_rev (Complex.logTaylor 7 s) (Complex.log (1+s))] at h
  linarith
 refine ⟨he,?_⟩
 have h:=norm_sub_le_norm_sub_add_norm_sub (Complex.logTaylor 7 s) s 0
 simp only [sub_zero] at h
 linarith

lemma geom_bound (s:ℂ) (hs:‖s‖≤1/10000000) :
 ‖(∑j∈Finset.range 7,(-s)^j)-1‖≤6/10000000 := by
 rw [show 7=6+1 by decide,Finset.sum_range_succ']
 simp only [pow_zero,add_sub_cancel_right]
 apply (norm_sum_le _ _).trans
 calc
  _ ≤ ∑j∈Finset.range 6,(1/10000000:ℝ) := by
   apply Finset.sum_le_sum
   intro j hj
   rw [norm_pow,norm_neg,pow_succ]
   have hp:‖s‖^j≤1:=pow_le_one₀ (norm_nonneg _) (by linarith)
   exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (by simpa using hs)
  _ = _ := by norm_num

lemma delta_guard (T t:ℝ) (hT:3000000000≤T ∧ T≤3300000000) (ht:|t|≤256) :
 ‖delta T t (Real.log (T/2)/2-1/(48*T^2))‖≤1/10000 := by
 let v:=z T 0
 let u:ℂ:=((t/2:ℝ):ℂ)*I
 let s:=u/v
 let L:=Complex.logTaylor 7 s
 let ω:=Real.log (T/2)/2-1/(48*T^2)
 have ht':-256≤t ∧ t≤256:=abs_le.mp ht
 have hT0:0<T:=by linarith [hT.1]
 have hvn:(v:ℂ)≠0:=by intro h;have hi:=congrArg Complex.re h;norm_num [v,z] at hi
 have hvl:1500000000≤‖v‖ := by
  have h:=Complex.abs_im_le_norm v
  have hi:v.im=T/2:=by simp [v,z]
  rw [hi,abs_of_nonneg (by positivity:0≤T/2)] at h
  linarith [hT.1]

 have hu:‖u‖≤128 := by
  simp only [u,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_I,mul_one,abs_div]
  norm_num
  linarith
 have hs:‖s‖≤1/10000000 := by
  change ‖u/v‖≤1/10000000
  rw [norm_div]
  apply (div_le_iff₀ (by linarith:0<‖v‖)).mpr
  nlinarith
 have hvm:‖v-1/2‖≤2000000000 := by
  have he:v-1/2=(-1/4:ℂ)+((T/2:ℝ):ℂ)*I:=by dsimp [v,z];push_cast;ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity:0≤T/2)]
  norm_num
  linarith [hT.2]
 have hl:=log_poly_bounds s hs
 have hc:‖u*(Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I))+
    I*(t:ℂ)/(48*(T:ℂ)^2)‖≤1/10^6 := by
  have hlog:‖Complex.log v-((Real.log (T/2):ℂ)+((Real.pi/2:ℝ):ℂ)*I)‖≤1/10^9:=by
   simpa only [v,z,add_zero] using log_bound (T/2) (by linarith [hT.1])
  have hd:‖I*(t:ℂ)/(48*(T:ℂ)^2)‖≤1/10^9 := by
   have he:‖I*(t:ℂ)/(48*(T:ℂ)^2)‖=|t|/(48*T^2) := by
    rw [norm_div,norm_mul,norm_mul,norm_pow,norm_I,Complex.norm_real,Real.norm_eq_abs]
    norm_num
   rw [he]
   apply (div_le_iff₀ (by positivity:0<48*T^2)).mpr
   nlinarith only [ht,hT.1,sq_nonneg (T-3000000000)]

  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hp:=mul_le_mul hu hlog (norm_nonneg _) (by norm_num)
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
 have h1:‖(v-1/2)*(L-s)‖≤(2000000000:ℝ)*(2/10^14) := by
  rw [norm_mul]
  exact mul_le_mul hvm hl.1 (norm_nonneg _) (by norm_num)
 have h2:‖u*L‖≤(128:ℝ)*(2/10000000) := by
  rw [norm_mul]
  exact mul_le_mul hu hl.2 (norm_nonneg _) (by norm_num)
 have h3:‖u/(2*v)‖≤1/10000000 := by
  rw [norm_div]
  have hd:‖(2:ℂ)*v‖=2*‖v‖:=by rw [norm_mul];norm_num
  rw [hd]
  apply (div_le_iff₀ (by linarith:0<2*‖v‖)).mpr
  nlinarith
 have h4:‖(1/(12*v))*((∑j∈Finset.range 7,(-s)^j)-1)‖≤1/10^12 := by
  rw [norm_mul,norm_div,norm_one,norm_mul,norm_ofNat]
  have hg:=geom_bound s hs
  have hi:(1:ℝ)/(12*‖v‖)≤1/(12*1500000000) :=
   div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  exact (mul_le_mul hi hg (norm_nonneg _) (by norm_num)).trans (by norm_num)
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
end RHFastUniformGammaPolynomialProofGuard
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset CauSeq
namespace RHFastUniformGammaPolynomialProof
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

lemma norm_G (T t:ℝ) : ‖G T t‖≤6 := by
 have h:=TaoFivePrimes.rh_high_height_scaled_gamma_bound.1 ((T+t)/2)
 simp only [G,z,norm_mul,Complex.norm_exp,Complex.ofReal_re]
 convert h using 1 <;> congr 2 <;> ring

lemma stirling_error (T t:ℝ) (h:2000000000≤T+t) : ‖G T t-C T t‖≤1/10^25 := by
 have hz:0<(z T t).re:=by simp [z]
 have hi:1000000000≤(z T t).im:=by simp [z];linarith
 have he:=TaoFivePrimes.rh_high_height_complex_stirling.2 (z T t) hz (by linarith)
 have heq:G T t-C T t=(Complex.Gamma (z T t)-Complex.exp (S (z T t)))*
   Complex.exp (((Real.pi*(T+t)/4:ℝ):ℂ)) := by
  unfold G C
  rw [Complex.exp_add]
  ring
 rw [heq,norm_mul,Complex.norm_exp,Complex.ofReal_re]
 have hG:‖Complex.Gamma (z T t)‖*Real.exp (Real.pi*(T+t)/4)≤6 := by
  simpa only [G,norm_mul,Complex.norm_exp,Complex.ofReal_re] using norm_G T t
 have he':‖Complex.Gamma (z T t)-Complex.exp (S (z T t))‖≤2*‖Complex.Gamma (z T t)‖/(z T t).im^3:=he
 calc
  _ ≤ (2*‖Complex.Gamma (z T t)‖/(z T t).im^3)*Real.exp (Real.pi*(T+t)/4) :=
    mul_le_mul_of_nonneg_right he' (Real.exp_pos _).le
  _ = 2*(‖Complex.Gamma (z T t)‖*Real.exp (Real.pi*(T+t)/4))/(z T t).im^3 := by ring
  _ ≤ 12/(1000000000:ℝ)^3 := by gcongr <;> linarith
  _ ≤ _ := by norm_num

lemma tail_bound (T t:ℝ) (hT:3000000000≤T ∧ T≤3300000000) (ht:|t|≤256) :
 ‖tail T t‖≤1/10^38 := by
 let v:=z T 0
 let u:ℂ:=((t/2:ℝ):ℂ)*I
 have hv:0<v.re:=by simp [v,z]
 have ht': -256≤t ∧ t≤256:=abs_le.mp ht
 have hzi:1500000000≤‖v‖ := by
  have h:=Complex.abs_im_le_norm v
  have hi:v.im=T/2:=by simp [v,z]
  rw [hi,abs_of_nonneg (by linarith [hT.1]:0≤T/2)] at h
  linarith [hT.1]
 have hu:‖u‖≤128 := by
  simp only [u,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_I,mul_one,abs_div,
    abs_of_pos (by norm_num:0<(2:ℝ))]
  linarith
 have hr:‖u/v‖≤1/10000000 := by
  rw [norm_div]
  apply (div_le_iff₀ (by linarith:0<‖v‖)).mpr
  nlinarith
 have he:v+u=z T t := by dsimp [v,u,z];push_cast;ring
 have hl:1000000000≤‖v+u‖ := by
  have h:=Complex.abs_im_le_norm (v+u)
  rw [he] at h
  have hi:(z T t).im=(T+t)/2:=by simp [z]
  rw [hi,abs_of_nonneg (by linarith:0≤(T+t)/2)] at h
  rw [he]
  linarith [hT.1]
 have hs:‖v+u-1/2‖≤3000000000 := by
  have hs':v+u-1/2=(-1/4:ℂ)+(((T+t)/2:ℝ):ℂ)*I := by dsimp [v,u,z];push_cast;ring
  rw [hs']
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith:0≤(T+t)/2)]
  norm_num
  linarith [hT.2]
 have hb:=TaoFivePrimes.rh_fast_center_stirling_increment v u hv hr hs hl
 have hid:tail T t=
  ((v+u-1/2)*Complex.log (v+u)-(v+u)+1/(12*(v+u)))-
    ((v-1/2)*Complex.log v-v+1/(12*v))-
    (u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
      (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)) := by
  unfold tail S P
  rw [←he]
  dsimp [v,u]
  ring
 rw [hid]
 exact hb

lemma exp_factorial_remainder (w:ℂ) (n:Nat) :
 ‖Complex.exp w-∑k∈Finset.range n,w^k/(k.factorial:ℂ)‖≤
   (‖w‖^n/(n.factorial:ℝ))*Real.exp ‖w‖ := by
 rw [←CauSeq.lim_const (abv:=norm) (∑k∈Finset.range n,w^k/(k.factorial:ℂ)),
   Complex.exp,sub_eq_add_neg,←CauSeq.lim_neg]
 rw [CauSeq.lim_add (Complex.exp' w) (-CauSeq.const norm (∑k∈Finset.range n,w^k/(k.factorial:ℂ))),
   ←Complex.lim_norm]
 refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n,fun j hj=>?_⟩)
 simp_rw [←sub_eq_add_neg]
 change ‖(∑k∈Finset.range j,w^k/(k.factorial:ℂ))-∑k∈Finset.range n,w^k/(k.factorial:ℂ)‖≤_
 let m:=j-n
 have he:j=n+m:=(Nat.add_sub_of_le hj).symm
 rw [he,Finset.sum_range_add_sub_sum_range]
 calc
  _ ≤ ∑k∈Finset.range m,‖w^(n+k)/((n+k).factorial:ℂ)‖:=norm_sum_le _ _
  _ ≤ ∑k∈Finset.range m,(‖w‖^n/(n.factorial:ℝ))*(‖w‖^k/(k.factorial:ℝ)) := by
   apply Finset.sum_le_sum
   intro k hk
   simp only [norm_div,Complex.norm_pow,norm_natCast,pow_add,norm_mul]
   rw [div_mul_div_comm]
   apply div_le_div_of_nonneg_left (by positivity) (by positivity)
   exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n k)
  _ = (‖w‖^n/(n.factorial:ℝ))*(∑k∈Finset.range m,‖w‖^k/(k.factorial:ℝ)) := by rw [Finset.mul_sum]
  _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (norm_nonneg w) m) (by positivity)

lemma exponential_error (d e:ℂ) (hd:‖d‖≤1/10000) (he:‖e-d‖≤1/10^38) :
 ‖Complex.exp e-∑k∈Finset.range 5,d^k/(k.factorial:ℂ)‖≤3/10^22 := by
 have hd1:‖d‖≤1:=by linarith
 have hen:‖e-d‖≤1:=by linarith
 have hnorm:‖Complex.exp d‖≤3 :=
  (Complex.norm_exp_le_exp_norm _).trans ((Real.exp_le_exp.mpr hd1).trans Real.exp_one_lt_three.le)
 have hp:‖Complex.exp e-Complex.exp d‖≤6/10^38 := by
  have hid:Complex.exp e-Complex.exp d=Complex.exp d*(Complex.exp (e-d)-1) := by
   rw [mul_sub,mul_one,←Complex.exp_add]
   congr 1
   ring
  rw [hid,norm_mul]
  calc
   _ ≤ 3*(2*‖e-d‖) := mul_le_mul hnorm (Complex.norm_exp_sub_one_le hen) (norm_nonneg _) (by norm_num)
   _ ≤ 6/10^38 := by linarith
 have ht:‖Complex.exp d-∑k∈Finset.range 5,d^k/(k.factorial:ℂ)‖≤(1/10000:ℝ)^5/120*3 := by
  apply (exp_factorial_remainder d 5).trans
  have hpow:=pow_le_pow_left₀ (norm_nonneg d) hd 5
  have hexp:Real.exp ‖d‖≤3:=(Real.exp_le_exp.mpr hd1).trans Real.exp_one_lt_three.le
  convert mul_le_mul (div_le_div_of_nonneg_right hpow (show (0:ℝ)≤120 by norm_num)) hexp
    (show (0:ℝ)≤Real.exp ‖d‖ from (Real.exp_pos _).le) (by positivity) using 1 <;> norm_num
 exact (norm_sub_le_norm_sub_add_norm_sub _ (Complex.exp d) _).trans (by linarith)

lemma carrier_norm (t ω:ℝ) : ‖carrier t ω‖≤1 := by
 rw [carrier,Complex.norm_exp]
 have he:((( -t^2/800:ℝ):ℂ)+I*(ω:ℂ)*t).re= -t^2/800:=by simp [pow_two]
 rw [he]
 exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])

lemma final_error (T t ω:ℝ) (hT:3000000000≤T ∧ T≤3300000000) (ht:|t|≤256)
 (A:ℂ) (hA:‖G T 0-A‖≤1/10^25) (hd:‖delta T t ω‖≤1/10000) :
 ‖G T t*(Real.exp (-t^2/800):ℂ)-A*carrier t ω*
   (∑k∈Finset.range 5,(delta T t ω)^k/(k.factorial:ℂ))‖≤1/10^20 := by
 have ht':-256≤t ∧ t≤256:=abs_le.mp ht
 have hst:=stirling_error T t (by linarith [hT.1])
 have hs0:=stirling_error T 0 (by linarith [hT.1])
 have htail:=tail_bound T t hT ht
 have hca:‖C T 0-A‖≤2/10^25 :=
  (norm_sub_le_norm_sub_add_norm_sub _ (G T 0) _).trans
   (by rw [norm_sub_rev (C T 0)];linarith)
 have hAn:‖A‖≤7 := by
  have h:=norm_sub_le_norm_sub_add_norm_sub A (G T 0) 0
  simp only [sub_zero,norm_sub_rev A] at h
  linarith [norm_G T 0]
 let e:=delta T t ω+tail T t
 have he:‖e-delta T t ω‖≤1/10^38 := by simpa only [e,add_sub_cancel_left] using htail
 have hen:‖e‖≤1 := (norm_add_le _ _).trans (by linarith)
 have hexp:‖Complex.exp e‖≤3 :=
  (Complex.norm_exp_le_exp_norm _).trans ((Real.exp_le_exp.mpr hen).trans Real.exp_one_lt_three.le)
 have hpoly:=exponential_error (delta T t ω) e hd he
 have hc:=carrier_norm t ω
 have hg:‖(Real.exp (-t^2/800):ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
 have hid:C T t*(Real.exp (-t^2/800):ℂ)=C T 0*carrier t ω*Complex.exp e := by
  unfold C carrier e delta tail
  rw [Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring
 have hdecomp:G T t*(Real.exp (-t^2/800):ℂ)-A*carrier t ω*
     (∑k∈Finset.range 5,(delta T t ω)^k/(k.factorial:ℂ))=
   (G T t-C T t)*(Real.exp (-t^2/800):ℂ)+(C T 0-A)*carrier t ω*Complex.exp e+
     A*carrier t ω*(Complex.exp e-∑k∈Finset.range 5,(delta T t ω)^k/(k.factorial:ℂ)) := by
  linear_combination hid
 rw [hdecomp]
 apply norm_add₃_le.trans
 simp only [norm_mul]
 have h1:‖G T t-C T t‖*‖(Real.exp (-t^2/800):ℂ)‖≤1/10^25 :=
  (mul_le_mul hst hg (norm_nonneg _) (by positivity)).trans_eq (by ring)
 have h2:‖C T 0-A‖*‖carrier t ω‖*‖Complex.exp e‖≤6/10^25 := by
  calc
   _ ≤ (2/10^25:ℝ)*1*3:=mul_le_mul (mul_le_mul hca hc (norm_nonneg _) (by positivity)) hexp (norm_nonneg _) (by positivity)
   _ = _ := by ring
 have h3:‖A‖*‖carrier t ω‖*‖Complex.exp e-∑k∈Finset.range 5,(delta T t ω)^k/(k.factorial:ℂ)‖≤21/10^22 := by
  calc
   _ ≤ 7*1*(3/10^22:ℝ):=mul_le_mul (mul_le_mul hAn hc (norm_nonneg _) (by norm_num)) hpoly (norm_nonneg _) (by norm_num)
   _ = _ := by ring
 linarith
end RHFastUniformGammaPolynomialProof
namespace RHFastUniformGammaPolynomialProofUniform
noncomputable def anchor (T:Nat) : ℂ :=
 let a:=RHFastKernelGammaArithmetic.compute T 8192
 let q:ℂ:=((a.cos:ℂ)+(a.sin:ℂ)*Complex.I)/(RHFastKernelLogData.D:ℂ)
 let phase:ℂ:=if a.negative then starRingEnd ℂ q else q
 ((a.amplitude:ℂ)/(RHFastKernelLogData.D:ℂ))*phase^8
lemma anchor_error (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) :
 ‖Complex.Gamma (1/4+(((T:ℝ)/2:ℝ):ℂ)*Complex.I)*
   Complex.exp (((Real.pi*(T:ℝ)/4:ℝ):ℂ))-anchor T‖≤1/10^25 := by
 have h:=TaoFivePrimes.rh_fast_kernel_gamma_uniform_analytic T 8192 hT (by omega) (by decide)
 dsimp only at h
 norm_num only [Nat.cast_ofNat,Int.cast_ofNat] at h
 have hb:(((T:Int)*32).toNat)=T*32 := by omega
 simp only [add_zero,sub_zero,hb] at h

 change ‖_-anchor T‖≤_ at h
 convert! h using 1 <;> (try congr 3) <;> (try congr 1) <;> (push_cast <;> ring)
end RHFastUniformGammaPolynomialProofUniform

theorem solution (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000)
 (t:ℝ) (ht:|t|≤256) :
 let a:=RHFastKernelGammaArithmetic.compute T 8192
 let q:ℂ:=((a.cos:ℂ)+(a.sin:ℂ)*Complex.I)/(RHFastKernelLogData.D:ℂ)
 let phase:ℂ:=if a.negative then starRingEnd ℂ q else q
 let A:ℂ:=((a.amplitude:ℂ)/(RHFastKernelLogData.D:ℂ))*phase^8
 let ω:ℝ:=Real.log ((T:ℝ)/2)/2-1/(48*(T:ℝ)^2)
 let v:ℂ:=1/4+(((T:ℝ)/2:ℝ):ℂ)*Complex.I
 let u:ℂ:=((t/2:ℝ):ℂ)*Complex.I
 let d:ℂ:=u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
     (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)+
     ((Real.pi*t/4:ℝ):ℂ)-Complex.I*(ω:ℂ)*t
 ‖Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*((T:ℝ)+t)/4-t^2/800:ℝ):ℂ))-
  A*Complex.exp (((-t^2/800:ℝ):ℂ)+Complex.I*(ω:ℂ)*t)*
    (∑k∈Finset.range 5,d^k/(k.factorial:ℂ))‖≤1/10^20 := by
 have hTr:3000000000≤(T:ℝ) ∧ (T:ℝ)≤3300000000 := by
  constructor
  · exact_mod_cast (show 3000000000≤T by omega)
  · exact_mod_cast hU
 have hd:=RHFastUniformGammaPolynomialProofGuard.delta_guard (T:ℝ) t hTr ht
 have hA:=RHFastUniformGammaPolynomialProofUniform.anchor_error T hT hU
 have hA':‖RHFastUniformGammaPolynomialProof.G (T:ℝ) 0-RHFastUniformGammaPolynomialProofUniform.anchor T‖≤1/10^25:=by
  simpa only [RHFastUniformGammaPolynomialProof.G,RHFastUniformGammaPolynomialProof.z,add_zero] using hA
 have hd':‖RHFastUniformGammaPolynomialProof.delta (T:ℝ) t (Real.log ((T:ℝ)/2)/2-1/(48*(T:ℝ)^2))‖≤1/10000:=by
  simpa only [RHFastUniformGammaPolynomialProofGuard.delta,RHFastUniformGammaPolynomialProofGuard.P,RHFastUniformGammaPolynomialProofGuard.z,
    RHFastUniformGammaPolynomialProof.delta,RHFastUniformGammaPolynomialProof.P,RHFastUniformGammaPolynomialProof.z,add_zero] using hd
 have he:=RHFastUniformGammaPolynomialProof.final_error (T:ℝ) t
  (Real.log ((T:ℝ)/2)/2-1/(48*(T:ℝ)^2)) hTr ht
  (RHFastUniformGammaPolynomialProofUniform.anchor T) hA' hd'
 have heq:RHFastUniformGammaPolynomialProof.G (T:ℝ) t*(Real.exp (-t^2/800):ℂ)=
   Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*Complex.I)*
     Complex.exp (((Real.pi*((T:ℝ)+t)/4-t^2/800:ℝ):ℂ)) := by
  unfold RHFastUniformGammaPolynomialProof.G RHFastUniformGammaPolynomialProof.z
  rw [mul_assoc,Complex.ofReal_exp,←Complex.exp_add]
  congr 2
  push_cast
  ring
 rw [heq] at he
 simpa only [RHFastUniformGammaPolynomialProofUniform.anchor,RHFastUniformGammaPolynomialProof.carrier,RHFastUniformGammaPolynomialProof.delta,
   RHFastUniformGammaPolynomialProof.P,RHFastUniformGammaPolynomialProof.z,add_zero] using he

#print axioms solution
