-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_gaussian_polynomial_fourier
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:54:08.547953+00:00
-- url     : https://prove2.me/submissions/e27848b7-7c00-4384-ad90-30cf9e29aec9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex MeasureTheory
open scoped FourierTransform
namespace RHFastGaussianFourier

noncomputable def f (h ω : ℝ) (n : Nat) (t : ℝ) : ℂ :=
  (t:ℂ)^n*Complex.exp (-(t:ℂ)^2/(2*(h:ℂ)^2)+Complex.I*(ω:ℂ)*t)

lemma integrable (h ω : ℝ) (hh:0<h) (n:Nat) : Integrable (f h ω n) := by
  have hr:=integrable_rpow_mul_exp_neg_mul_sq
    (b:=1/(2*h^2)) (s:=(n:ℝ)) (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hi:Integrable (fun t:ℝ=>|t|^n*Real.exp (-t^2/(2*h^2))) := by
    convert hr.norm using 1
    ext t
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),Real.rpow_natCast,
      abs_pow]
    congr 2
    ring
  apply hi.mono'
  · unfold f
    exact (by unfold f;fun_prop : Continuous (f h ω n)).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [f,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp]
    have he:(-(t:ℂ)^2/(2*(h:ℂ)^2)+Complex.I*(ω:ℂ)*t).re= -t^2/(2*h^2) := by
      rw [show -(t:ℂ)^2/(2*(h:ℂ)^2)=((-t^2/(2*h^2):ℝ):ℂ) by push_cast;rfl]
      simp only [add_re,mul_re,ofReal_re,ofReal_im,I_re,I_im]
      ring
    rw [he]

lemma derivative_zero (h ω t:ℝ) :
 HasDerivAt (f h ω 0) ((Complex.I*(ω:ℂ))*f h ω 0 t-
    (1/(h:ℂ)^2)*f h ω 1 t) t := by
  have hd:=(((((hasDerivAt_id t).ofReal_comp).pow 2).neg.div_const (2*(h:ℂ)^2)).add
    (((hasDerivAt_id t).ofReal_comp).const_mul (Complex.I*(ω:ℂ)))).cexp
  convert! hd using 1 <;> (try funext s) <;>
    (dsimp [f] <;> norm_num <;> ring)

lemma derivative_succ (h ω t:ℝ) (n:Nat) :
 HasDerivAt (f h ω (n+1))
   (((n+1:Nat):ℂ)*f h ω n t+Complex.I*(ω:ℂ)*f h ω (n+1) t-
    (1/(h:ℂ)^2)*f h ω (n+2) t) t := by
  have hp:HasDerivAt (fun t:ℝ=>(t:ℂ)^(n+1))
    (((n+1:Nat):ℂ)*(t:ℂ)^n) t := by
    simpa using! ((hasDerivAt_id t).ofReal_comp).pow (n+1)
  have he:=derivative_zero h ω t
  have hd:=hp.mul he
  convert! hd using 1 <;> (try funext s) <;>
    (dsimp [f] <;> simp only [pow_zero,one_mul,pow_succ] <;> ring)

lemma twist_integrable {g:ℝ→ℂ} (hg:Integrable g) (x:ℝ) :
 Integrable (fun t:ℝ=>Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)*g t) := by
 apply hg.norm.mono'
 · exact (by fun_prop : Continuous (fun t:ℝ=>Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I))).aestronglyMeasurable.mul hg.aestronglyMeasurable
 · filter_upwards [] with t
   simp [norm_mul,Complex.norm_exp]
lemma fourier_sub {g j:ℝ→ℂ} (hg:Integrable g) (hj:Integrable j) (x:ℝ) :
  𝓕 (fun t=>g t-j t) x=𝓕 g x-𝓕 j x := by
 simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul,mul_sub]
 exact integral_sub (twist_integrable hg x) (twist_integrable hj x)
lemma fourier_add {g j:ℝ→ℂ} (hg:Integrable g) (hj:Integrable j) (x:ℝ) :
  𝓕 (fun t=>g t+j t) x=𝓕 g x+𝓕 j x := by
 simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul,mul_add]
 exact integral_add (twist_integrable hg x) (twist_integrable hj x)
lemma fourier_const_mul (c:ℂ) (g:ℝ→ℂ) (x:ℝ) :
  𝓕 (fun t=>c*g t) x=c*𝓕 g x := by
 simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
 simp_rw [mul_left_comm _ c]
 exact integral_const_mul c _

lemma recurrence_zero (h ω x:ℝ) (hh:0<h) :
  𝓕 (f h ω 1) x=(h:ℂ)^2*Complex.I*((ω:ℂ)-2*Real.pi*x)*𝓕 (f h ω 0) x := by
  have he:deriv (f h ω 0)=(fun t=>Complex.I*(ω:ℂ)*f h ω 0 t-
      (1/(h:ℂ)^2)*f h ω 1 t) := funext (fun t=>(derivative_zero h ω t).deriv)
  have hi:Integrable (deriv (f h ω 0)) := by
    rw [he]
    exact ((integrable h ω hh 0).const_mul _).sub ((integrable h ω hh 1).const_mul _)
  have hd:Differentiable ℝ (f h ω 0):=fun t=>(derivative_zero h ω t).differentiableAt
  have hf:=congrFun (Real.fourier_deriv (integrable h ω hh 0) hd hi) x
  rw [he,fourier_sub ((integrable h ω hh 0).const_mul _)
    ((integrable h ω hh 1).const_mul _),fourier_const_mul,fourier_const_mul] at hf
  simp only [smul_eq_mul] at hf
  have hn:(h:ℂ)≠0:=by exact_mod_cast hh.ne'
  field_simp [hn] at hf ⊢
  linear_combination -hf

lemma recurrence (h ω x:ℝ) (hh:0<h) (n:Nat) :
  𝓕 (f h ω (n+2)) x=(h:ℂ)^2*(Complex.I*((ω:ℂ)-2*Real.pi*x)*𝓕 (f h ω (n+1)) x+
    ((n+1:Nat):ℂ)*𝓕 (f h ω n) x) := by
  have he:deriv (f h ω (n+1))=(fun t=>
    ((n+1:Nat):ℂ)*f h ω n t+Complex.I*(ω:ℂ)*f h ω (n+1) t-
    (1/(h:ℂ)^2)*f h ω (n+2) t) := funext (fun t=>(derivative_succ h ω t n).deriv)
  have hi:Integrable (deriv (f h ω (n+1))) := by
    rw [he]
    exact (((integrable h ω hh n).const_mul _).add
      ((integrable h ω hh (n+1)).const_mul _)).sub ((integrable h ω hh (n+2)).const_mul _)
  have hd:Differentiable ℝ (f h ω (n+1)):=fun t=>(derivative_succ h ω t n).differentiableAt
  have hf:=congrFun (Real.fourier_deriv (integrable h ω hh (n+1)) hd hi) x
  rw [he,fourier_sub (g:=fun t=>((n+1:Nat):ℂ)*f h ω n t+Complex.I*(ω:ℂ)*f h ω (n+1) t) (j:=fun t=>(1/(h:ℂ)^2)*f h ω (n+2) t) (((integrable h ω hh n).const_mul _).add
      ((integrable h ω hh (n+1)).const_mul _)) ((integrable h ω hh (n+2)).const_mul _),
    fourier_add ((integrable h ω hh n).const_mul _)
      ((integrable h ω hh (n+1)).const_mul _)] at hf
  simp only [fourier_const_mul,smul_eq_mul] at hf
  have hn:(h:ℂ)≠0:=by exact_mod_cast hh.ne'
  field_simp [hn] at hf ⊢
  linear_combination -hf

lemma hermite_derivative (n:Nat) :
  Polynomial.derivative (Polynomial.hermite (n+1))=
    Polynomial.C ((n+1:Nat):Int)*Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_one,Polynomial.hermite_zero]
  | succ n ih =>
    rw [Polynomial.hermite_succ (n+1),Polynomial.derivative_sub,
      Polynomial.derivative_mul,Polynomial.derivative_X,one_mul,ih]
    simp only [Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,zero_add]
    rw [Polynomial.hermite_succ n]
    simp only [Nat.cast_add,Nat.cast_one,map_add,map_one]
    ring

lemma hermite_recurrence (n:Nat) :
 Polynomial.hermite (n+2)=Polynomial.X*Polynomial.hermite (n+1)-
   Polynomial.C ((n+1:Nat):Int)*Polynomial.hermite n := by
 rw [show n+2=(n+1)+1 by omega,Polynomial.hermite_succ,hermite_derivative]

lemma gaussian_factor (h:ℝ) (hh:0<h) :
 ((Real.pi:ℂ)/(1/(2*(h:ℂ)^2)))^(1/2:ℂ)=(Real.sqrt (2*Real.pi):ℂ)*(h:ℂ) := by
 have he:(Real.pi:ℂ)/(1/(2*(h:ℂ)^2))=((2*Real.pi*h^2:ℝ):ℂ):=by push_cast;field_simp <;> ring
 rw [he]
 have hx:(0:ℝ)≤2*Real.pi*h^2:=by positivity
 rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hx,←Real.sqrt_eq_rpow]
 rw [Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh,Complex.ofReal_mul]

lemma base (h ω x:ℝ) (hh:0<h) :
  𝓕 (f h ω 0) x=(Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
    Complex.exp (-(((h*(2*Real.pi*x-ω):ℝ):ℂ)^2)/2) := by
 rw [Real.fourier_real_eq_integral_exp_smul]
 simp only [smul_eq_mul,f,pow_zero,one_mul,←Complex.exp_add]
 have he (t:ℝ):(((-2*Real.pi*t*x:ℝ):ℂ)*I)+
   (-(t:ℂ)^2/(2*(h:ℂ)^2)+I*(ω:ℂ)*t)=
   (-1/(2*(h:ℂ)^2))*(t:ℂ)^2+(I*((ω:ℂ)-2*Real.pi*x))*t+0 := by push_cast;ring
 simp_rw [he]
 have hb:(-1/(2*(h:ℂ)^2)).re<0 := by
  rw [show (-1/(2*(h:ℂ)^2))=((-1/(2*h^2):ℝ):ℂ) by push_cast;rfl,Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
 rw [integral_cexp_quadratic hb]
 rw [show -(-1/(2*(h:ℂ)^2))=1/(2*(h:ℂ)^2) by ring,gaussian_factor h hh]
 congr 1
 congr 1
 have hn:(h:ℂ)≠0:=by exact_mod_cast hh.ne'
 push_cast
 field_simp [hn]
 ring_nf
 simp [I_sq] <;> ring

lemma all_moments (h ω x:ℝ) (hh:0<h) (n:Nat) :
  𝓕 (f h ω n) x=(Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*(-I*(h:ℂ))^n*
    Polynomial.aeval (((h*(2*Real.pi*x-ω):ℝ):ℂ)) (Polynomial.hermite n)*
    Complex.exp (-(((h*(2*Real.pi*x-ω):ℝ):ℂ)^2)/2) := by
 induction n using Nat.twoStepInduction with
 | zero => simpa [Polynomial.hermite_zero] using base h ω x hh
 | one =>
   rw [recurrence_zero h ω x hh,base h ω x hh]
   simp only [Polynomial.hermite_one,Polynomial.aeval_X,pow_one]
   push_cast
   ring
 | more n hn hn1 =>
   rw [recurrence h ω x hh n,hn,hn1,hermite_recurrence]
   simp only [map_sub,map_mul,Polynomial.aeval_X,Polynomial.aeval_C]
   push_cast
   simp only [pow_succ]
   ring_nf
   simp only [I_sq]
   ring

end RHFastGaussianFourier

theorem solution (h ω x:ℝ) (hh:0<h) (n:Nat) :
  𝓕 (fun t:ℝ=>(t:ℂ)^n*Complex.exp (-(t:ℂ)^2/(2*(h:ℂ)^2)+
    Complex.I*(ω:ℂ)*t)) x=
    (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*(-Complex.I*(h:ℂ))^n*
      Polynomial.aeval (((h*(2*Real.pi*x-ω):ℝ):ℂ)) (Polynomial.hermite n)*
      Complex.exp (-(((h*(2*Real.pi*x-ω):ℝ):ℂ)^2)/2) :=
  RHFastGaussianFourier.all_moments h ω x hh n
#print axioms solution
