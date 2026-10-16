-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_center_gamma_polynomial_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T23:06:14.318311+00:00
-- url     : https://prove2.me/submissions/c737e584-2b7f-4826-a8f2-06d6e6088c2a

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_fast_center_stirling_increment
import Theorems.Thm_TaoFivePrimes_rh_high_height_complex_stirling
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset CauSeq
namespace RHFastCenterGamma
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
end RHFastCenterGamma

theorem solution (T t ω:ℝ) (hT:3000000000≤T ∧ T≤3300000000) (ht:|t|≤256)
 (A:ℂ)
 (hA:‖Complex.Gamma (1/4+((T/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*T/4:ℝ):ℂ))-A‖≤1/10^25)
 (hd:
   let v:ℂ:=1/4+((T/2:ℝ):ℂ)*Complex.I
   let u:ℂ:=((t/2:ℝ):ℂ)*Complex.I
   ‖u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
     (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)+
     ((Real.pi*t/4:ℝ):ℂ)-Complex.I*(ω:ℂ)*t‖≤1/10000) :
 let v:ℂ:=1/4+((T/2:ℝ):ℂ)*Complex.I
 let u:ℂ:=((t/2:ℝ):ℂ)*Complex.I
 let d:=u*(Complex.log v-1)+(v+u-1/2)*Complex.logTaylor 7 (u/v)+
     (1/(12*v))*((∑j∈Finset.range 7,(-u/v)^j)-1)+
     ((Real.pi*t/4:ℝ):ℂ)-Complex.I*(ω:ℂ)*t
 ‖Complex.Gamma (1/4+(((T+t)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*(T+t)/4-t^2/800:ℝ):ℂ))-
  A*Complex.exp (((-t^2/800:ℝ):ℂ)+Complex.I*(ω:ℂ)*t)*
    (∑k∈Finset.range 5,d^k/(k.factorial:ℂ))‖≤1/10^20 := by
 have hA':‖RHFastCenterGamma.G T 0-A‖≤1/10^25:=by simpa only [RHFastCenterGamma.G,RHFastCenterGamma.z,add_zero] using hA
 have hd':‖RHFastCenterGamma.delta T t ω‖≤1/10000:=by
  simpa only [RHFastCenterGamma.delta,RHFastCenterGamma.P,RHFastCenterGamma.z,add_zero] using hd
 have h:=RHFastCenterGamma.final_error T t ω hT ht A hA' hd'
 have heq:RHFastCenterGamma.G T t*(Real.exp (-t^2/800):ℂ)=
   Complex.Gamma (1/4+(((T+t)/2:ℝ):ℂ)*Complex.I)*
     Complex.exp (((Real.pi*(T+t)/4-t^2/800:ℝ):ℂ)) := by
  unfold RHFastCenterGamma.G RHFastCenterGamma.z
  rw [mul_assoc,Complex.ofReal_exp,←Complex.exp_add]
  congr 2
  push_cast
  ring
 rw [heq] at h
 simpa only [RHFastCenterGamma.carrier,RHFastCenterGamma.delta,RHFastCenterGamma.P,
   RHFastCenterGamma.z,add_zero] using h
#print axioms solution
