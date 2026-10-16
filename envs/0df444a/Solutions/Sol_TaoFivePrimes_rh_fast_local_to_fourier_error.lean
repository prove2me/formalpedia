-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_local_to_fourier_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T23:20:04.256542+00:00
-- url     : https://prove2.me/submissions/da52066f-1171-4cf6-b042-b6b6b2bb8191

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex MeasureTheory Set
open scoped FourierTransform
namespace RHFastLocalToFourier
lemma exp_tail : Real.exp (-64)≤1/10^20 := by
 have h:=Real.pow_div_factorial_le_exp (64:ℝ) (by norm_num) 64
 have hbig:(10:ℝ)^20≤Real.exp 64 := (by norm_num : (10:ℝ)^20≤64^64/(64).factorial).trans h
 rw [Real.exp_neg]
 rw [inv_eq_one_div]
 apply (div_le_iff₀ (Real.exp_pos 64)).mpr
 nlinarith

lemma integral_error (e:ℝ→ℂ) (he:Integrable e)
 (hl:∀t:ℝ,|t|≤256 → ‖e t‖≤81/10^20)
 (ht:∀t:ℝ,256≤|t| → ‖e t‖≤41*Real.exp (-|t|/4)) :
 ‖∫t:ℝ,e t‖≤1/10^15 := by
 have hleft:‖∫t:ℝ in Iic (-256),e t‖≤164*Real.exp (-64) := by
  have hb:IntegrableOn (fun t:ℝ=>41*Real.exp ((1/4:ℝ)*t)) (Iic (-256)) :=
   (integrableOn_exp_mul_Iic (a:=1/4) (by norm_num) (-256)).const_mul 41
  have hn:‖∫t:ℝ in Iic (-256),e t‖≤∫t:ℝ in Iic (-256),41*Real.exp ((1/4:ℝ)*t) := by
   apply norm_integral_le_of_norm_le hb
   filter_upwards [ae_restrict_mem measurableSet_Iic] with t htm
   change t≤(-256:ℝ) at htm
   have ht0:t≤0:=by linarith [htm]
   have heq:-|t|/4=(1/4:ℝ)*t:=by rw [abs_of_nonpos ht0];ring
   have h:=ht t (by rw [abs_of_nonpos ht0];linarith [htm])
   simpa only [heq] using h
  apply hn.trans_eq
  rw [integral_const_mul,integral_exp_mul_Iic (by norm_num)]
  norm_num <;> ring
 have hright:‖∫t:ℝ in Ioi 256,e t‖≤164*Real.exp (-64) := by
  have hb:IntegrableOn (fun t:ℝ=>41*Real.exp ((-1/4:ℝ)*t)) (Ioi 256) :=
   (integrableOn_exp_mul_Ioi (a:=-1/4) (by norm_num) 256).const_mul 41
  have hn:‖∫t:ℝ in Ioi 256,e t‖≤∫t:ℝ in Ioi 256,41*Real.exp ((-1/4:ℝ)*t) := by
   apply norm_integral_le_of_norm_le hb
   filter_upwards [ae_restrict_mem measurableSet_Ioi] with t htm
   change (256:ℝ)<t at htm
   have ht0:0≤t:=by linarith [htm]
   have heq:-|t|/4=(-1/4:ℝ)*t:=by rw [abs_of_nonneg ht0];ring
   have h:=ht t (by rw [abs_of_nonneg ht0];linarith [htm])
   simpa only [heq] using h
  apply hn.trans_eq
  rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num)]
  norm_num <;> ring
 have hmiddle:‖∫t:ℝ in (-256)..256,e t‖≤512*(81/10^20:ℝ) := by
  have hb:∀t∈Set.uIoc (-256:ℝ) 256,‖e t‖≤81/10^20 := by
   intro t htm
   apply hl
   simp only [Set.uIoc_of_le (by norm_num:(-256:ℝ)≤256),Set.mem_Ioc] at htm
   exact abs_le.mpr ⟨htm.1.le,htm.2⟩
  apply (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans_eq
  norm_num

 have hwhole:=intervalIntegral.integral_Iic_add_Ioi (b:=256) he.integrableOn he.integrableOn
 have hmid:=intervalIntegral.integral_Iic_sub_Iic (a:=-256) (b:=256) he.integrableOn he.integrableOn
 have heq:(∫t:ℝ,e t)=(∫t:ℝ in Iic (-256),e t)+(∫t:ℝ in (-256)..256,e t)+
    (∫t:ℝ in Ioi 256,e t) := by linear_combination hmid-hwhole
 rw [heq]
 apply norm_add₃_le.trans
 have hsmall:=exp_tail
 linarith

lemma twist_integrable {g:ℝ→ℂ} (hg:Integrable g) (x:ℝ) :
 Integrable (fun t:ℝ=>Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)*g t) := by
 apply hg.norm.mono'
 · exact (by fun_prop : Continuous (fun t:ℝ=>Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I))).aestronglyMeasurable.mul hg.aestronglyMeasurable
 · filter_upwards [] with t
   simp [Complex.norm_exp]

lemma fourier_error (f g:ℝ→ℂ) (hf:Integrable f) (hg:Integrable g)
 (hl:∀t:ℝ,|t|≤256 → ‖f t-g t‖≤81/10^20)
 (ht:∀t:ℝ,256≤|t| → ‖f t-g t‖≤41*Real.exp (-|t|/4)) (x:ℝ) :
 ‖𝓕 f x-𝓕 g x‖≤1/10^15 := by
 let e:ℝ→ℂ:=fun t=>Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)*(f t-g t)
 have he:Integrable e:=twist_integrable (hf.sub hg) x
 have hn (t:ℝ):‖e t‖=‖f t-g t‖:=by simp [e,Complex.norm_exp]
 have h:=integral_error e he (by intro t htm;rw [hn];exact hl t htm)
   (by intro t htm;rw [hn];exact ht t htm)
 have heq:𝓕 f x-𝓕 g x=∫t:ℝ,e t := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [←integral_sub (twist_integrable hf x) (twist_integrable hg x)]
  simp only [e,mul_sub]
 rw [heq]
 exact h
end RHFastLocalToFourier
theorem solution (f g:ℝ→ℂ) (hf:Integrable f) (hg:Integrable g)
 (hl:∀t:ℝ,|t|≤256 → ‖f t-g t‖≤81/10^20)
 (ht:∀t:ℝ,256≤|t| → ‖f t-g t‖≤41*Real.exp (-|t|/4)) (x:ℝ) :
 ‖𝓕 f x-𝓕 g x‖≤1/10^15 := RHFastLocalToFourier.fourier_error f g hf hg hl ht x
#print axioms solution
