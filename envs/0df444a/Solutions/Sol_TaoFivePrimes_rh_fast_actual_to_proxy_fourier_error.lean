-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_actual_to_proxy_fourier_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T09:55:27.01109+00:00
-- url     : https://prove2.me/submissions/efebe95c-9ba6-4af5-b70e-abf07affdf3f

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Theorems.Thm_TaoFivePrimes_rh_fast_center_gamma_polynomial_uniform
import Theorems.Thm_TaoFivePrimes_rh_fast_center_proxy_moment_tail
import Theorems.Thm_TaoFivePrimes_rh_fast_local_to_fourier_half_error
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex MeasureTheory Set
open scoped FourierTransform
namespace RHFastActualFourierError
open RHFastGaussianWindow
noncomputable def gammaGaussian (T:Nat) (t:ℝ) : ℂ :=
 Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*I)*
 Complex.exp (((Real.pi*((T:ℝ)+t)/4-t^2/800:ℝ):ℂ))
noncomputable def actualMoment (T k:Nat) (t:ℝ) : ℂ :=gammaGaussian T t*momentFactor k t
lemma gamma_continuous (T:Nat) : Continuous (gammaGaussian T) := by
 have hc:Continuous (fun t:ℝ=>Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · fun_prop
  · intro m hm
    have hz:0<(1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*I).re:=by simp
    rw [hm] at hz
    have hmr:(0:ℝ) ≤ m := by positivity
    simp only [neg_re,natCast_re] at hz
    linarith
 unfold gammaGaussian
 exact hc.mul (by fun_prop)
lemma gamma_norm (T:Nat) (t:ℝ) : ‖gammaGaussian T t‖≤6*Real.exp (-t^2/800) := by
 have hg:=TaoFivePrimes.rh_high_height_scaled_gamma_bound.1 (((T:ℝ)+t)/2)
 have hg':‖Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*I)‖*
   Real.exp (Real.pi*((T:ℝ)+t)/4)≤6 := by
  convert! hg using 1 <;> congr 2 <;> ring
 unfold gammaGaussian
 rw [norm_mul,Complex.norm_exp]
 simp only [ofReal_re]
 rw [show Real.pi*((T:ℝ)+t)/4-t^2/800=Real.pi*((T:ℝ)+t)/4+(-t^2/800) by ring,Real.exp_add,←mul_assoc]
 exact mul_le_mul_of_nonneg_right hg' (Real.exp_pos _).le
lemma factor_bound (k:Nat) (t:ℝ) : ‖momentFactor k t‖≤Real.exp (|t|/64) := by
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
 simp only [momentFactor,norm_div,norm_pow,norm_mul,Complex.norm_natCast,norm_ofNat,hn]
 rw [he]
 have hp:=Real.pow_div_factorial_le_exp (Real.pi*|t|/256) (by positivity) k
 apply hp.trans
 apply Real.exp_le_exp.mpr
 nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr Real.pi_lt_four.le)]

lemma actual_norm (T k:Nat) (t:ℝ) :
 ‖actualMoment T k t‖≤6*Real.exp (|t|/64-t^2/800) := by
 rw [actualMoment,norm_mul]
 calc
  _ ≤ (6*Real.exp (-t^2/800))*Real.exp (|t|/64) :=
   mul_le_mul (gamma_norm T t) (factor_bound k t) (norm_nonneg _) (by positivity)
  _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring
lemma actual_tail (T k:Nat) (t:ℝ) (ht:256≤|t|) :
 ‖actualMoment T k t‖≤6*Real.exp (-|t|/4) := by
 apply (actual_norm T k t).trans
 apply mul_le_mul_of_nonneg_left _ (by norm_num)
 apply Real.exp_le_exp.mpr
 nlinarith [sq_abs t,mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
lemma actual_integrable (T k:Nat) : Integrable (actualMoment T k) := by
 have hi:Integrable (fun t:ℝ=>Real.exp (-t^2/1600)) := by
  convert integrable_exp_neg_mul_sq (by norm_num:(0:ℝ)<1/1600) using 1
  ext t
  congr 1
  ring
 have hc:Continuous (actualMoment T k):=by
  unfold actualMoment
  exact (gamma_continuous T).mul (by unfold momentFactor;fun_prop)
 apply (hi.const_mul (6*Real.exp 1)).mono' hc.aestronglyMeasurable
 filter_upwards [] with t
 apply (actual_norm T k t).trans
 have he:|t|/64-t^2/800≤1-t^2/1600 := by
  nlinarith [sq_abs t,sq_nonneg (|t|-25/2)]
 calc
  _ ≤ 6*Real.exp (1-t^2/1600):=by gcongr
  _ = _ := by rw [show 1-t^2/1600=1+(-t^2/1600) by ring,Real.exp_add];ring
lemma proxy_continuous (T k:Nat) : Continuous (momentProxy T k) := by
 unfold momentProxy proxy carrier exponentialPolynomial delta momentFactor Complex.logTaylor
 fun_prop
lemma proxy_integrable (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) :
 Integrable (momentProxy T k) := by
 have hc:=proxy_continuous T k
 have hl:IntegrableOn (momentProxy T k) (Iic (-256)) := by
  have hb:IntegrableOn (fun t:ℝ=>35*Real.exp ((1/4:ℝ)*t)) (Iic (-256)) :=
   (integrableOn_exp_mul_Iic (a:=1/4) (by norm_num) (-256)).const_mul 35
  apply hb.mono' hc.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Iic] with t htm
  change t≤(-256:ℝ) at htm
  have ht0:t≤0:=by linarith
  have h:=TaoFivePrimes.rh_fast_center_proxy_moment_tail T hT hU k t
   (by rw [abs_of_nonpos ht0];linarith)
  convert! h using 1
  rw [abs_of_nonpos ht0]
  congr 2
  ring
 have hr:IntegrableOn (momentProxy T k) (Ioi 256) := by
  have hb:IntegrableOn (fun t:ℝ=>35*Real.exp ((-1/4:ℝ)*t)) (Ioi 256) :=
   (integrableOn_exp_mul_Ioi (a:=-1/4) (by norm_num) 256).const_mul 35
  apply hb.mono' hc.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t htm
  change (256:ℝ)<t at htm
  have ht0:0≤t:=by linarith
  have h:=TaoFivePrimes.rh_fast_center_proxy_moment_tail T hT hU k t
   (by rw [abs_of_nonneg ht0];linarith)
  convert! h using 1
  rw [abs_of_nonneg ht0]
  congr 2
  ring
 have hm:IntegrableOn (momentProxy T k) (Icc (-256) 256):=hc.integrableOn_Icc
 have hu:Iic (-256:ℝ) ∪ Icc (-256:ℝ) 256 ∪ Ioi (256:ℝ)=univ := by
  ext t
  simp only [mem_union,mem_Iic,mem_Icc,mem_Ioi,mem_univ,iff_true]
  by_cases h:t≤(-256:ℝ)
  · exact Or.inl (Or.inl h)
  by_cases h2:t≤(256:ℝ)
  · exact Or.inl (Or.inr ⟨by linarith,h2⟩)
  · exact Or.inr (by linarith)
 have hall:IntegrableOn (momentProxy T k) univ:=by rw [←hu];exact (hl.union hm).union hr
 exact integrableOn_univ.mp hall
lemma local_error (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (t:ℝ)
 (ht:|t|≤256) : ‖actualMoment T k t-momentProxy T k t‖≤81/10^20 := by
 have hp:=TaoFivePrimes.rh_fast_center_gamma_polynomial_uniform T hT hU t ht
 change ‖gammaGaussian T t-proxy T t‖≤1/10^20 at hp
 have he4:Real.exp 4≤81 := by
  calc
   _ = (Real.exp 1)^4:=by rw [←Real.exp_nat_mul];norm_num
   _ ≤ (3:ℝ)^4:=pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 4
   _ = _ := by norm_num
 have hf:‖momentFactor k t‖≤81 := by
  apply (factor_bound k t).trans
  exact (Real.exp_le_exp.mpr (by linarith)).trans he4
 unfold actualMoment momentProxy
 rw [←sub_mul,norm_mul]
 exact (mul_le_mul hp hf (norm_nonneg _) (by norm_num)).trans_eq (by ring)
lemma error (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (x:ℝ) :
 ‖𝓕 (actualMoment T k) x-𝓕 (momentProxy T k) x‖≤1/(2*10^15) := by
 apply TaoFivePrimes.rh_fast_local_to_fourier_half_error _ _ (actual_integrable T k)
  (proxy_integrable T hT hU k) (local_error T hT hU k) _ x
 intro t ht
 have h:=norm_sub_le (actualMoment T k t) (momentProxy T k t)
 have ha:=actual_tail T k t ht
 have hb:=TaoFivePrimes.rh_fast_center_proxy_moment_tail T hT hU k t ht
 linarith
end RHFastActualFourierError

theorem solution (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (x:ℝ) :
 ‖𝓕 (fun t:ℝ=>Complex.Gamma (1/4+((((T:ℝ)+t)/2:ℝ):ℂ)*Complex.I)*
    Complex.exp (((Real.pi*((T:ℝ)+t)/4-t^2/800:ℝ):ℂ))*RHFastGaussianWindow.momentFactor k t) x-
 𝓕 (RHFastGaussianWindow.momentProxy T k) x‖≤1/(2*10^15) :=
 RHFastActualFourierError.error T hT hU k x
#print axioms solution
