-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_platt_fourier_identity
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T20:08:37.745285+00:00
-- url     : https://prove2.me/submissions/56be74fc-a0ea-4dfe-9fca-63ce70401921

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaFourier
noncomputable def logKernel (s : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-(Real.exp y:ℂ)+s*(y:ℂ))
lemma gamma_log_integral (s : ℂ) (hs : 0<s.re) :
    Complex.Gamma s=∫ y : ℝ, logKernel s y := by
  rw [Complex.Gamma_eq_integral hs,Complex.GammaIntegral]
  have hi := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ: Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (Real.exp (-u):ℂ)*(u:ℂ)^(s-1))
  have him : Real.exp '' (Set.univ:Set ℝ)=Ioi 0 := by
    simpa using Real.range_exp
  rw [him] at hi
  rw [hi]
  simp only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp,Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add]
  unfold logKernel
  congr 1
  push_cast
  ring
lemma gaussian_factor (h : ℝ) (hh : 0<h) :
    ((Real.pi:ℂ)/(1/(2*(h:ℂ)^2)))^(1/2:ℂ)=(Real.sqrt (2*Real.pi):ℂ)*(h:ℂ) := by
  have he : (Real.pi:ℂ)/(1/(2*(h:ℂ)^2))=((2*Real.pi*h^2:ℝ):ℂ) := by push_cast;field_simp <;> ring
  rw [he]
  have hx : (0:ℝ)≤2*Real.pi*h^2 := by positivity
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hx,←Real.sqrt_eq_rpow]
  rw [Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh,Complex.ofReal_mul]
lemma exponential_gaussian_fourier (h : ℝ) (hh : 0<h) (a x : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (-(t:ℂ)^2/(2*(h:ℂ)^2)+(a:ℂ)*t)) x=
      (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
        Complex.exp ((h:ℂ)^2/2*((a:ℂ)-2*(Real.pi:ℂ)*I*x)^2) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul,←Complex.exp_add]
  have he (t : ℝ) : ((-2*Real.pi*t*x:ℝ):ℂ)*I+
      (-(t:ℂ)^2/(2*(h:ℂ)^2)+(a:ℂ)*t)=
      (-1/(2*(h:ℂ)^2))*(t:ℂ)^2+((a:ℂ)-2*(Real.pi:ℂ)*I*x)*t+0 := by push_cast;ring
  simp_rw [he]
  have hb : (-1/(2*(h:ℂ)^2)).re<0 := by
    have he : (-1/(2*(h:ℂ)^2))=((-1/(2*h^2):ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  rw [integral_cexp_quadratic hb]
  have hf : -( -1/(2*(h:ℂ)^2))=1/(2*(h:ℂ)^2) := by ring
  rw [hf,gaussian_factor h hh]
  congr 1
  congr 1
  field_simp
  ring
lemma log_kernel_exp_rewrite (s : ℂ) (y : ℝ) :
    (Real.exp y) • ((Real.exp (-Real.exp y):ℂ)*(Real.exp y:ℂ)^(s-1))=logKernel s y := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp,Complex.ofReal_exp,←Complex.exp_add,←Complex.exp_add]
  unfold logKernel
  congr 1
  push_cast
  ring
lemma log_kernel_integrable (s : ℂ) (hs : 0<s.re) : Integrable (logKernel s) := by
  have he : Real.exp '' (Set.univ:Set ℝ)=Ioi 0 := by simpa using Real.range_exp
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (Real.exp (-u):ℂ)*(u:ℂ)^(s-1))).mp
      (he.symm ▸ Complex.GammaIntegral_convergent hs)
  simpa only [IntegrableOn,Measure.restrict_univ,abs_of_pos (Real.exp_pos _),
    log_kernel_exp_rewrite] using hi
noncomputable def window (T h t : ℝ) : ℂ :=
  Complex.exp ((Real.pi*(t+T)/4-t^2/(2*h^2):ℝ):ℂ)
noncomputable def gammaWindow (T h t : ℝ) : ℂ :=
  Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*window T h t
noncomputable def Q (T h x y : ℝ) : ℂ :=
  (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
    Complex.exp ((Real.pi*T/4:ℝ)+((h:ℂ)^2/2)*
      ((Real.pi/4:ℝ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2)
noncomputable def joint (T h x t y : ℝ) : ℂ :=
  logKernel (1/4+(((t+T)/2:ℝ):ℂ)*I) y*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma window_integrable (T h : ℝ) (hh : 0<h) : Integrable (window T h) := by
  have hb : (-(1/(2*(h:ℂ)^2))).re<0 := by
    have he : (-(1/(2*(h:ℂ)^2)))=((-1/(2*h^2):ℝ):ℂ) := by push_cast;ring
    rw [he,ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have he (t : ℝ) : window T h t=Complex.exp (
    (-(1/(2*(h:ℂ)^2)))*(t:ℂ)^2+(Real.pi/4:ℝ)*t+(Real.pi*T/4:ℝ)) := by
    unfold window
    congr 1
    push_cast
    ring
  change Integrable (fun t : ℝ => window T h t)
  simp_rw [he]
  exact integrable_cexp_quadratic' hb _ _
lemma log_kernel_norm (s : ℂ) (y : ℝ) :
    ‖logKernel s y‖=Real.exp (-Real.exp y+s.re*y) := by
  rw [logKernel,Complex.norm_exp]
  congr 1
  simp only [add_re,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
lemma joint_norm (T h x t y : ℝ) :
    ‖joint T h x t y‖=‖window T h t‖*‖logKernel (1/4) y‖ := by
  unfold joint
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one,log_kernel_norm,log_kernel_norm]
  have hr : (1/4+(((t+T)/2:ℝ):ℂ)*I:ℂ).re=(1/4:ℂ).re := by simp
  rw [hr]
  ring
lemma joint_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => joint T h x p.1 p.2) := by
  have hm := (window_integrable T h hh).norm.mul_prod
    (log_kernel_integrable (1/4) (by norm_num)).norm
  apply hm.mono'
  · have hc : Continuous (fun p : ℝ×ℝ => joint T h x p.1 p.2) := by
      unfold joint logKernel window
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    exact (joint_norm T h x p.1 p.2).le
lemma inner_joint (T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, joint T h x t y)=
      Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  let b : ℂ := -1/(2*(h:ℂ)^2)
  let c : ℂ := (Real.pi/4:ℝ)+I*((y/2-2*Real.pi*x:ℝ):ℂ)
  let d : ℂ := (-Real.exp y+y/4+Real.pi*T/4:ℝ)+I*(T:ℂ)*y/2
  have hb : b.re<0 := by
    have he : b=((-1/(2*h^2):ℝ):ℂ) := by dsimp [b];push_cast;ring
    rw [he,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have he (t : ℝ) : joint T h x t y=Complex.exp (b*(t:ℂ)^2+c*t+d) := by
    unfold joint logKernel window
    rw [←Complex.exp_add,←Complex.exp_add]
    congr 1
    dsimp [b,c,d]
    push_cast
    ring
  simp_rw [he]
  rw [integral_cexp_quadratic hb]
  have hn : -b=1/(2*(h:ℂ)^2) := by dsimp [b];ring
  rw [hn,gaussian_factor h hh]
  have hr : d-c^2/(4*b)=((-Real.exp y+y/4:ℝ):ℂ)+
      ((Real.pi*T/4:ℝ)+((h:ℂ)^2/2)*c^2+I*(T:ℂ)*y/2) := by
    dsimp [b,d]
    push_cast
    field_simp
    ring
  rw [hr,Complex.exp_add]
  dsimp [Q,c]
  ring
lemma gamma_window_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (gammaWindow T h) x=
      ∫ y : ℝ, Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  have hi (t : ℝ) : (∫ y : ℝ, joint T h x t y)=
      Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*window T h t*
        Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [joint,integral_mul_const]
    rw [←gamma_log_integral _ (by norm_num)]
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ, ∫ y : ℝ, joint T h x t y := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      dsimp [gammaWindow]
      ring
    _ = ∫ y : ℝ, ∫ t : ℝ, joint T h x t y :=
      integral_integral_swap (joint_integrable T h x hh)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact inner_joint T h x y hh
end RHHighGammaFourier

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaFourier
noncomputable def dirichletWeight (T a : ℝ) : ℂ :=
  Complex.exp (-(1/2+I*(T:ℂ))*(Real.log a:ℂ))
lemma Q_translation (T h x y a : ℝ) (ha : 0<a) :
    Q T h (x+Real.log a/(2*Real.pi)) (y+2*Real.log a)=
      Q T h x y*Complex.exp (I*(T:ℂ)*(Real.log a:ℂ)) := by
  unfold Q
  have he : ((y+2*Real.log a)/2-2*Real.pi*(x+Real.log a/(2*Real.pi)):ℝ)=
      y/2-2*Real.pi*x := by field_simp;ring
  rw [he]
  conv_rhs => rw [mul_assoc,←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma gamma_fourier_dirichlet_shift (T h x a : ℝ) (hh : 0<h) (ha : 0<a) :
    dirichletWeight T a*𝓕 (gammaWindow T h) (x+Real.log a/(2*Real.pi))=
      ∫ y : ℝ, Complex.exp ((-a^2*Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  rw [gamma_window_fourier T h _ hh]
  rw [←integral_const_mul]
  have ht := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun y : ℝ =>
    dirichletWeight T a*(Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*
      Q T h (x+Real.log a/(2*Real.pi)) y)) (2*Real.log a)
  rw [←ht]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [Q_translation T h x y a ha]
  have hexp : Real.exp (y+2*Real.log a)=a^2*Real.exp y := by
    rw [Real.exp_add,show 2*Real.log a=Real.log a+Real.log a by ring,Real.exp_add,Real.exp_log ha]
    ring
  rw [hexp]
  unfold dirichletWeight
  have he : -(1/2+I*(T:ℂ))*(Real.log a:ℂ)+
      ((-a^2*Real.exp y+(y+2*Real.log a)/4:ℝ):ℂ)+
      I*(T:ℂ)*(Real.log a:ℂ)=((-a^2*Real.exp y+y/4:ℝ):ℂ) := by push_cast;ring
  calc
    _ = (Complex.exp (-(1/2+I*(T:ℂ))*(Real.log a:ℂ))*
      Complex.exp ((-a^2*Real.exp y+(y+2*Real.log a)/4:ℝ):ℂ)*
      Complex.exp (I*(T:ℂ)*(Real.log a:ℂ)))*Q T h x y := by ring
    _ = _ := by rw [←Complex.exp_add,←Complex.exp_add,he]
end RHHighGammaFourier

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set HurwitzZeta Filter Asymptotics
open scoped FourierTransform Topology
namespace RHHighThetaFourier
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0
lemma modif_convergent (s : ℂ) : MellinConvergent P.f_modif s := by
  exact mellinConvergent_of_isBigO_rpow P.hf_modif_int
    (P.isStrongFEPair_toStrongFEPair.hf_top (-(s.re+1))) (by linarith)
    (P.isStrongFEPair_toStrongFEPair.hf_zero (-(s.re-1))) (by linarith)
lemma modif_one_lt (t : ℝ) (ht : 1<t) :
    P.f_modif t=(evenKernel 0 t:ℂ)-1 := by
  simp [P,WeakFEPair.f_modif,hurwitzEvenFEPair,ht,not_lt.2 ht.le,Set.indicator_of_notMem]
lemma modif_lt_one (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    P.f_modif t=(evenKernel 0 t:ℂ)-(t^(-(1:ℝ)/2):ℝ) := by
  simp [P,WeakFEPair.f_modif,hurwitzEvenFEPair,ht,ht1,not_lt.2 ht1.le]
  norm_num
noncomputable def logMellin (s : ℂ) (y : ℝ) : ℂ :=
  P.f_modif (Real.exp y)*Complex.exp (s*(y:ℂ))
lemma modif_log_rewrite (s : ℂ) (y : ℝ) :
    (Real.exp y) • ((Real.exp y:ℂ)^(s-1)*P.f_modif (Real.exp y))=logMellin s y := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne')]
  rw [←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  rw [Complex.real_smul,Complex.ofReal_exp]
  unfold logMellin
  have he : Complex.exp (y:ℂ)*Complex.exp ((y:ℂ)*(s-1))=Complex.exp (s*(y:ℂ)) := by
    rw [←Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (y:ℂ)*Complex.exp ((y:ℂ)*(s-1)))*P.f_modif (Real.exp y) := by ring
    _ = _ := by rw [he];ring
lemma modif_log_integrable (s : ℂ) : Integrable (logMellin s) := by
  have he : Real.exp '' (Set.univ:Set ℝ)=Ioi 0 := by simpa using Real.range_exp
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (u:ℂ)^(s-1)*P.f_modif u)).mp (he.symm ▸ modif_convergent s)
  simpa only [IntegrableOn,Measure.restrict_univ,abs_of_pos (Real.exp_pos _),modif_log_rewrite] using hi
lemma completed_log_mellin (s : ℂ) :
    completedRiemannZeta₀ s=(∫ y : ℝ, logMellin (s/2) y)/2 := by
  have hi := integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ (fun y (_ : y ∈ (Set.univ:Set ℝ)) => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    (fun x _ y _ h => Real.exp_injective h)
    (fun u : ℝ => (u:ℂ)^(s/2-1)*P.f_modif u)
  have he : Real.exp '' (Set.univ:Set ℝ)=Ioi 0 := by simpa using Real.range_exp
  rw [he] at hi
  have hd : completedRiemannZeta₀ s=mellin P.f_modif (s/2)/2 := rfl
  rw [hd,mellin]
  simp only [smul_eq_mul]
  rw [hi]
  simp only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _),modif_log_rewrite]
open RHHighGammaFourier
noncomputable def thetaJoint (T h x t y : ℝ) : ℂ :=
  (logMellin ((1/2+((t+T:ℝ):ℂ)*I)/2) y/2)*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma log_mellin_norm (s : ℂ) (y : ℝ) :
    ‖logMellin s y‖=‖P.f_modif (Real.exp y)‖*Real.exp (s.re*y) := by
  rw [logMellin,norm_mul,Complex.norm_exp]
  simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
lemma theta_joint_norm (T h x t y : ℝ) :
    ‖thetaJoint T h x t y‖=‖window T h t‖*(‖logMellin (1/4) y‖/2) := by
  unfold thetaJoint
  rw [norm_mul,norm_mul,norm_div,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one,log_mellin_norm,log_mellin_norm]
  norm_num
  ring
lemma theta_joint_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => thetaJoint T h x p.1 p.2) := by
  have hm := (window_integrable T h hh).norm.mul_prod
    ((modif_log_integrable (1/4)).norm.div_const 2)
  apply hm.mono'
  · have hf := P.hf_modif_int.aestronglyMeasurable
    have hm : AEStronglyMeasurable (fun y : ℝ => P.f_modif (Real.exp y)) volume := by
      have hi := modif_log_integrable (0:ℂ)
      convert! hi.aestronglyMeasurable using 1
      ext y
      simp [logMellin]
    have he : Continuous (fun p : ℝ×ℝ =>
      Complex.exp (((1/2+((p.1+T:ℝ):ℂ)*I)/2)*(p.2:ℂ))/2*window T h p.1*
        Complex.exp (((-2*Real.pi*p.1*x:ℝ):ℂ)*I)) := by unfold window;fun_prop
    have hmeas : AEStronglyMeasurable (fun p : ℝ×ℝ =>
      P.f_modif (Real.exp p.2)*(Complex.exp (((1/2+((p.1+T:ℝ):ℂ)*I)/2)*(p.2:ℂ))/2*window T h p.1*
        Complex.exp (((-2*Real.pi*p.1*x:ℝ):ℂ)*I))) (volume.prod volume) :=
      hm.comp_snd.mul he.aestronglyMeasurable
    convert! hmeas using 1
    ext p
    dsimp [thetaJoint,logMellin]
    ring
  · filter_upwards [] with p
    exact (theta_joint_norm T h x p.1 p.2).le
lemma theta_joint_factor (T h x t y : ℝ) :
    thetaJoint T h x t y=
      (P.f_modif (Real.exp y)*Complex.exp (Real.exp y:ℂ)/2)*joint T h x t y := by
  unfold thetaJoint logMellin joint logKernel
  have he : ((1/2+((t+T:ℝ):ℂ)*I)/2)*(y:ℂ)=
      (Real.exp y:ℂ)+(-(Real.exp y:ℂ)+(1/4+(((t+T)/2:ℝ):ℂ)*I)*(y:ℂ)) := by
    push_cast
    ring
  rw [he,Complex.exp_add]
  ring
lemma theta_joint_inner (T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, thetaJoint T h x t y)=
      (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y := by
  simp_rw [theta_joint_factor]
  rw [integral_const_mul,inner_joint T h x y hh]
  have he : Complex.exp (Real.exp y:ℂ)*Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)=
      Complex.exp ((y/4:ℝ):ℂ) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (P.f_modif (Real.exp y)*(Complex.exp (Real.exp y:ℂ)*
      Complex.exp ((-Real.exp y+y/4:ℝ):ℂ))/2)*Q T h x y := by ring
    _ = _ := by rw [he]
noncomputable def entireWindow (T h t : ℝ) : ℂ :=
  completedRiemannZeta₀ (1/2+((t+T:ℝ):ℂ)*I)*window T h t
lemma entire_window_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (entireWindow T h) x=
      ∫ y : ℝ, (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y := by
  have hi (t : ℝ) : (∫ y : ℝ, thetaJoint T h x t y)=
      entireWindow T h t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [thetaJoint,integral_mul_const,integral_div]
    rw [←completed_log_mellin]
    rfl
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ, ∫ y : ℝ, thetaJoint T h x t y := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      simp only [smul_eq_mul,mul_comm]
    _ = ∫ y : ℝ, ∫ t : ℝ, thetaJoint T h x t y :=
      integral_integral_swap (theta_joint_integrable T h x hh)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact theta_joint_inner T h x y hh
end RHHighThetaFourier

set_option autoImplicit false
set_option maxHeartbeats 0
open Real MeasureTheory Set HurwitzZeta Filter
open scoped Topology
namespace RHHighThetaSeries
noncomputable def psi (u : ℝ) : ℝ := (evenKernel 0 u-1)/2
lemma hasSum_psi (u : ℝ) (hu : 0<u) :
    HasSum (fun n : Nat => Real.exp (-Real.pi*(n+1:ℝ)^2*u)) (psi u) := by
  have h := (hasSum_nat_cosKernel₀ 0 hu).div_const 2
  convert! h using 1
  · ext n
    simp
  · simp only [QuotientAddGroup.mk_zero]
    rw [←evenKernel_eq_cosKernel_of_zero]
    rfl
lemma psi_nonneg (u : ℝ) (hu : 0<u) : 0≤psi u := by
  rw [←(hasSum_psi u hu).tsum_eq]
  exact tsum_nonneg (fun n => (Real.exp_pos _).le)
lemma psi_le (u : ℝ) (hu : 0<u) : psi u≤1/(Real.pi*u) := by
  let q := Real.exp (-Real.pi*u)
  have hp : 0<Real.pi*u := mul_pos Real.pi_pos hu
  have hqp : 0<q := Real.exp_pos _
  have hq1 : q<1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hqn : ‖q‖<1 := by simpa only [Real.norm_eq_abs,abs_of_pos hqp] using hq1
  have hg : HasSum (fun n : Nat => q^(n+1)) (q/(1-q)) := by
    convert! (hasSum_geometric_of_norm_lt_one hqn).mul_left q using 1
    · ext n
      rw [pow_succ]
      ring
  have hb (n : Nat) : Real.exp (-Real.pi*(n+1:ℝ)^2*u)≤q^(n+1) := by
    have hn : 1≤(n+1:ℝ) := by have h := Nat.cast_nonneg (α:=ℝ) n; linarith
    have hpow : (n+1:ℝ)≤(n+1:ℝ)^2 := by nlinarith
    have he : q^(n+1)=Real.exp (-Real.pi*(n+1:ℝ)*u) := by
      dsimp [q]
      rw [←Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hpow hp.le]
  have hs : psi u≤q/(1-q) := by
    rw [←(hasSum_psi u hu).tsum_eq,←hg.tsum_eq]
    exact (hasSum_psi u hu).summable.tsum_le_tsum hb hg.summable
  have hexp : q*Real.exp (Real.pi*u)=1 := by
    dsimp [q]
    rw [←Real.exp_add]
    simp
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (Real.pi*u)) hqp.le
  rw [hexp] at he
  apply hs.trans
  apply (div_le_div_iff₀ (by linarith : 0<1-q) hp).mpr
  nlinarith
lemma finite_psi_sum_le (u : ℝ) (hu : 0<u) (N : Nat) :
    (∑ n ∈ Finset.range N, Real.exp (-Real.pi*(n+1:ℝ)^2*u))≤1/(Real.pi*u) := by
  apply le_trans _ (psi_le u hu)
  rw [←(hasSum_psi u hu).tsum_eq]
  exact (hasSum_psi u hu).summable.sum_le_tsum (Finset.range N) (fun n _ => (Real.exp_pos _).le)
end RHHighThetaSeries

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGammaFourier
lemma Q_norm (T h x y : ℝ) (hh : 0<h) :
    ‖Q T h x y‖=Real.sqrt (2*Real.pi)*h*
      Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2) := by
  rw [Q,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos hh,
    Complex.norm_exp]
  congr 1
  simp only [add_re,mul_re,div_re,ofReal_re,ofReal_im,I_re,I_im,pow_two]
  norm_num
  ring
lemma real_quadratic_integrable (b c d : ℝ) (hb : b<0) :
    Integrable (fun y : ℝ => Real.exp (b*y^2+c*y+d)) := by
  have h := (integrable_cexp_quadratic' (b:= (b:ℂ)) (by simpa using hb) (c:ℂ) (d:ℂ)).norm
  convert! h using 1
  ext y
  rw [Complex.norm_exp]
  congr 1
  simp only [←Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_add,Complex.ofReal_re]
noncomputable def Qmajorant (T h x y : ℝ) : ℝ :=
  (Real.sqrt (2*Real.pi)*h/Real.pi)*
    Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2-3*y/4)
lemma Qmajorant_integrable (T h x : ℝ) (hh : 0<h) : Integrable (Qmajorant T h x) := by
  have he (y : ℝ) : Qmajorant T h x y=(Real.sqrt (2*Real.pi)*h/Real.pi)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x-3/4)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    unfold Qmajorant
    congr 1
    congr 1
    ring
  change Integrable (fun y : ℝ => Qmajorant T h x y)
  simp_rw [he]
  exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
lemma Qweighted_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (fun y : ℝ => Real.exp (y/4)*‖Q T h x y‖) := by
  have he (y : ℝ) : Real.exp (y/4)*‖Q T h x y‖=
      (Real.sqrt (2*Real.pi)*h)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+1/4)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    rw [Q_norm T h x y hh]
    have hp : (y/4)+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
        (-h^2/8)*y^2+(h^2*Real.pi*x+1/4)*y+
          (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2) := by ring
    calc
      _ = (Real.sqrt (2*Real.pi)*h)*
        (Real.exp (y/4)*Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by ring
      _ = _ := by rw [←Real.exp_add,hp]
  simp_rw [he]
  exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
end RHHighGammaFourier

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighThetaGamma
open RHHighGammaFourier RHHighThetaSeries
noncomputable def seriesKernel (n : Nat) (T h x y : ℝ) : ℂ :=
  Complex.exp ((-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4:ℝ):ℂ)*Q T h x y
lemma series_kernel_norm (n : Nat) (T h x y : ℝ) :
    ‖seriesKernel n T h x y‖=
      Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4)*‖Q T h x y‖ := by
  rw [seriesKernel,norm_mul,Complex.norm_exp,Complex.ofReal_re]
lemma series_kernel_integrable (n : Nat) (T h x : ℝ) (hh : 0<h) :
    Integrable (seriesKernel n T h x) := by
  have hc : Continuous (seriesKernel n T h x) := by unfold seriesKernel Q;fun_prop
  apply (Qweighted_integrable T h x hh).mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  rw [series_kernel_norm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hp : 0≤Real.pi*(n+1:ℝ)^2*Real.exp y := by positivity
  linarith
lemma Qmajorant_eq (T h x y : ℝ) (hh : 0<h) :
    Qmajorant T h x y=
      (1/(Real.pi*Real.exp y))*(Real.exp (y/4)*‖Q T h x y‖) := by
  rw [Q_norm T h x y hh]
  have he : 1/(Real.pi*Real.exp y)=(1/Real.pi)*Real.exp (-y) := by
    rw [Real.exp_neg]
    ring
  rw [he]
  have hp : (-y)+(y/4)+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
      Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2-3*y/4 := by ring
  unfold Qmajorant
  calc
    _ = (1/Real.pi)*(Real.sqrt (2*Real.pi)*h)*
      (Real.exp (-y)*Real.exp (y/4)*Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by
      rw [←Real.exp_add,←Real.exp_add,hp]
      ring
    _ = _ := by ring
lemma finite_kernel_norm_le (T h x y : ℝ) (hh : 0<h) (N : Nat) :
    (∑ n ∈ Finset.range N, ‖seriesKernel n T h x y‖)≤Qmajorant T h x y := by
  simp_rw [series_kernel_norm]
  have he (n : Nat) : Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y+y/4)*‖Q T h x y‖=
      Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y)*(Real.exp (y/4)*‖Q T h x y‖) := by
    rw [Real.exp_add]
    ring
  simp_rw [he]
  rw [←Finset.sum_mul,Qmajorant_eq T h x y hh]
  exact mul_le_mul_of_nonneg_right (finite_psi_sum_le (Real.exp y) (Real.exp_pos _) N) (by positivity)
lemma kernel_integral_norm_summable (T h x : ℝ) (hh : 0<h) :
    Summable (fun n : Nat => ∫ y : ℝ, ‖seriesKernel n T h x y‖) := by
  apply summable_of_sum_range_le (fun n => integral_nonneg (fun y => norm_nonneg _))
  intro N
  rw [←integral_finset_sum (Finset.range N) (fun n _ => (series_kernel_integrable n T h x hh).norm)]
  exact integral_mono (integrable_finsetSum _ (fun n _ => (series_kernel_integrable n T h x hh).norm))
    (Qmajorant_integrable T h x hh) (fun y => finite_kernel_norm_le T h x y hh N)
lemma hasSum_kernel_point (T h x y : ℝ) :
    HasSum (fun n : Nat => seriesKernel n T h x y)
      ((psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y) := by
  have hbase : HasSum (fun n : Nat => (Real.exp (-Real.pi*(n+1:ℝ)^2*Real.exp y):ℂ))
      (psi (Real.exp y):ℂ) := hasSum_ofReal.mpr (hasSum_psi (Real.exp y) (Real.exp_pos _))
  have hsum := (hbase.mul_right (Complex.exp ((y/4:ℝ):ℂ))).mul_right (Q T h x y)
  convert! hsum using 1
  ext n
  unfold seriesKernel
  rw [Complex.ofReal_exp,←Complex.exp_add]
  congr 1
  push_cast
  ring
lemma sum_kernel_integral (T h x : ℝ) (hh : 0<h) :
    (∑' n : Nat, ∫ y : ℝ, seriesKernel n T h x y)=
      ∫ y : ℝ, (psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y := by
  have hsum := hasSum_integral_of_summable_integral_norm
    (fun n => series_kernel_integrable n T h x hh) (kernel_integral_norm_summable T h x hh)
  rw [hsum.tsum_eq]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (hasSum_kernel_point T h x y).tsum_eq
end RHHighThetaGamma

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighPoleFourier
open RHHighGammaFourier
noncomputable def sline (ε T t : ℝ) : ℂ := 1/2+(ε:ℂ)*I*(t+T:ℝ)
lemma sline_re (ε T t : ℝ) : (sline ε T t).re=1/2 := by simp [sline]
noncomputable def poleJoint (ε T h x t y : ℝ) : ℂ :=
  Complex.exp (-(sline ε T t/2)*(y:ℂ))*window T h t*
    Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma laplace_half (s : ℂ) (hs : 0<s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-(s/2)*(y:ℂ)))=2/s := by
  have h := integral_exp_mul_complex_Ioi (a:=-(s/2)) (by simp;linarith) 0
  simpa using h
lemma pole_joint_norm (ε T h x t y : ℝ) :
    ‖poleJoint ε T h x t y‖=‖window T h t‖*Real.exp (-y/4) := by
  rw [poleJoint,norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp]
  have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
  rw [he,Real.exp_zero,mul_one]
  have hr : (-(sline ε T t/2)*(y:ℂ)).re= -y/4 := by simp [sline];ring
  rw [hr]
  ring
lemma pole_joint_integrable (ε T h x : ℝ) (hh : 0<h) :
    Integrable (fun p : ℝ×ℝ => poleJoint ε T h x p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hy : IntegrableOn (fun y : ℝ => Real.exp (-y/4)) (Ioi 0) := by
    convert! integrableOn_exp_mul_Ioi (a:=(-1/4:ℝ)) (by norm_num) 0 using 1
    ext y
    congr 1
    ring
  have hm := (window_integrable T h hh).norm.mul_prod hy
  apply hm.mono'
  · have hc : Continuous (fun p : ℝ×ℝ => poleJoint ε T h x p.1 p.2) := by
      unfold poleJoint sline window
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    exact (pole_joint_norm ε T h x p.1 p.2).le
lemma pole_joint_factor (ε T h x t y : ℝ) :
    poleJoint ε T h x t y=
      Complex.exp ((Real.exp (-ε*y)-(-ε*y)/4-y/4:ℝ):ℂ)*joint T h x t (-ε*y) := by
  unfold poleJoint sline joint logKernel
  conv_rhs => rw [←mul_assoc,←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring
lemma pole_joint_inner (ε T h x y : ℝ) (hh : 0<h) :
    (∫ t : ℝ, poleJoint ε T h x t y)=
      Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-ε*y) := by
  simp_rw [pole_joint_factor]
  rw [integral_const_mul,inner_joint T h x (-ε*y) hh]
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring
noncomputable def poleWindow (ε T h t : ℝ) : ℂ := window T h t/sline ε T t
lemma pole_window_fourier (ε T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow ε T h) x=
      (1/2:ℂ)*∫ y : ℝ in Ioi 0, Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-ε*y) := by
  have hi (t : ℝ) : (1/2:ℂ)*(∫ y : ℝ in Ioi 0, poleJoint ε T h x t y)=
      poleWindow ε T h t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [poleJoint,integral_mul_const]
    rw [laplace_half _ (by rw [sline_re];norm_num)]
    unfold poleWindow
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = (1/2:ℂ)*∫ t : ℝ, ∫ y : ℝ in Ioi 0, poleJoint ε T h x t y := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      simp only [smul_eq_mul,mul_comm]
    _ = (1/2:ℂ)*∫ y : ℝ in Ioi 0, ∫ t : ℝ, poleJoint ε T h x t y := by
      rw [integral_integral_swap (pole_joint_integrable ε T h x hh)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      exact pole_joint_inner ε T h x y hh
end RHHighPoleFourier

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGammaFourier
lemma croot_of_pos (a : ℝ) (ha : 0<a) : (a:ℂ)^(1/2:ℂ)=(Real.sqrt a:ℂ) := by
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow ha.le,←Real.sqrt_eq_rpow]
lemma mass_prefactor (h : ℝ) (hh : 0<h) :
    (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*((Real.pi:ℂ)/(h^2/8))^(1/2:ℂ)/2=2*(Real.pi:ℂ) := by
  have he : (Real.pi:ℂ)/(h^2/8)=((8*Real.pi/h^2:ℝ):ℂ) := by push_cast;ring
  rw [he,croot_of_pos _ (by positivity)]
  have hs : Real.sqrt (8*Real.pi/h^2)=2*Real.sqrt (2*Real.pi)/h := by
    rw [Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh]
    rw [show (8*Real.pi:ℝ)=4*(2*Real.pi) by ring,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs]
  have hn : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
  have hs2 : (Real.sqrt (2*Real.pi):ℂ)^2=2*(Real.pi:ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  push_cast
  calc
    _ = (Real.sqrt (2*Real.pi):ℂ)^2 := by field_simp [hn] <;> ring
    _ = _ := hs2
lemma gaussian_pole_mass (T h x : ℝ) (hh : 0<h) :
    (1/2:ℂ)*(∫ y : ℝ, Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y)=
      2*(Real.pi:ℂ)*Complex.exp (
        ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by
  let b : ℂ := -(h:ℂ)^2/8
  let c : ℂ := ((h^2*Real.pi*x-1/4:ℝ):ℂ)+I*((h^2*Real.pi/8+T/2:ℝ):ℂ)
  let d : ℂ := ((Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2:ℝ):ℂ)-I*((h^2*Real.pi^2*x/2:ℝ):ℂ)
  have hb : b.re<0 := by
    have he : b=((-h^2/8:ℝ):ℂ) := by dsimp [b];push_cast;rfl
    rw [he,ofReal_re]
    nlinarith [sq_pos_of_pos hh]
  have he (y : ℝ) : Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y=
      (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*Complex.exp (b*(y:ℂ)^2+c*y+d) := by
    unfold Q
    have hp : ((-y/4:ℝ):ℂ)+((Real.pi*T/4:ℝ):ℂ)+((h:ℂ)^2/2)*
        (((Real.pi/4:ℝ):ℂ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2=
        b*(y:ℂ)^2+c*y+d := by dsimp [b,c,d];push_cast;ring_nf <;> simp only [Complex.I_sq] <;> ring
    calc
      _ = (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*
        (Complex.exp ((-y/4:ℝ):ℂ)*Complex.exp (
          ((Real.pi*T/4:ℝ):ℂ)+((h:ℂ)^2/2)*
          (((Real.pi/4:ℝ):ℂ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2)) := by ring
      _ = _ := by rw [←Complex.exp_add];congr 2;simpa only [add_assoc] using hp
  simp_rw [he]
  rw [integral_const_mul,integral_cexp_quadratic hb]
  have hn : -b=(h:ℂ)^2/8 := by dsimp [b];ring
  rw [hn]
  have he : d-c^2/(4*b)=
      ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
      I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ) := by
    dsimp [b,c,d]
    push_cast
    have hne : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
    field_simp [hne]
    ring_nf <;> simp only [Complex.I_sq] <;> ring
  rw [he]
  have hp := mass_prefactor h hh
  calc
    _ = ((Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*((Real.pi:ℂ)/(h^2/8))^(1/2:ℂ)/2)*
      Complex.exp (((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by ring
    _ = _ := by rw [hp]
end RHHighGammaFourier

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGammaFourier
lemma weighted_Q_integrable (c T h x : ℝ) (hh : 0<h) :
    Integrable (fun y : ℝ => Complex.exp ((c*y:ℝ):ℂ)*Q T h x y) := by
  have he (y : ℝ) : ‖Complex.exp ((c*y:ℝ):ℂ)*Q T h x y‖=
      (Real.sqrt (2*Real.pi)*h)*
      Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+c)*y+
        (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2)) := by
    rw [norm_mul,Complex.norm_exp,Complex.ofReal_re,Q_norm T h x y hh]
    have hp : c*y+(Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)=
        (-h^2/8)*y^2+(h^2*Real.pi*x+c)*y+
          (Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2) := by ring
    calc
      _ = (Real.sqrt (2*Real.pi)*h)*(Real.exp (c*y)*
        Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by ring
      _ = _ := by rw [←Real.exp_add,hp]
  have hi : Integrable (fun y : ℝ => ‖Complex.exp ((c*y:ℝ):ℂ)*Q T h x y‖) := by
    simp_rw [he]
    exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
  have hc : Continuous (fun y : ℝ => Complex.exp ((c*y:ℝ):ℂ)*Q T h x y) := by unfold Q;fun_prop
  exact (integrable_norm_iff hc.aestronglyMeasurable).mp hi
end RHHighGammaFourier
namespace RHHighThetaGamma
open RHHighGammaFourier RHHighThetaSeries
noncomputable def psiKernel (T h x y : ℝ) : ℂ :=
  (psi (Real.exp y):ℂ)*Complex.exp ((y/4:ℝ):ℂ)*Q T h x y
lemma psi_kernel_integrable (T h x : ℝ) (hh : 0<h) : Integrable (psiKernel T h x) := by
  have ht : Continuous (fun y : ℝ => HurwitzZeta.evenKernel 0 (Real.exp y)) :=
    (HurwitzZeta.continuousOn_evenKernel 0).comp_continuous Real.continuous_exp (fun y => Real.exp_pos y)
  have hc : Continuous (psiKernel T h x) := by
    have hp : Continuous (fun y : ℝ => psi (Real.exp y)) := by
      unfold psi
      exact (ht.sub continuous_const).div_const _
    unfold psiKernel Q
    fun_prop
  apply (Qmajorant_integrable T h x hh).mono' hc.aestronglyMeasurable
  filter_upwards [] with y
  rw [psiKernel,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (psi_nonneg (Real.exp y) (Real.exp_pos _)),Complex.norm_exp,Complex.ofReal_re]
  rw [Qmajorant_eq T h x y hh]
  have he : psi (Real.exp y)*Real.exp (y/4)*‖Q T h x y‖=
      psi (Real.exp y)*(Real.exp (y/4)*‖Q T h x y‖) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (psi_le (Real.exp y) (Real.exp_pos _)) (by positivity)
end RHHighThetaGamma

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighPlattFourier
open RHHighGammaFourier RHHighThetaFourier RHHighThetaGamma RHHighThetaSeries
open RHHighPoleFourier
noncomputable def dirichletTerm (T h x : ℝ) (n : Nat) : ℂ :=
  dirichletWeight T ((n+1:ℝ)*Real.sqrt Real.pi)*
    𝓕 (gammaWindow T h) (x+Real.log ((n+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi))
lemma dirichlet_term_eq (T h x : ℝ) (hh : 0<h) (n : Nat) :
    dirichletTerm T h x n=∫ y : ℝ, seriesKernel n T h x y := by
  unfold dirichletTerm
  rw [gamma_fourier_dirichlet_shift T h x _ hh (by positivity)]
  have he : ((n+1:ℝ)*Real.sqrt Real.pi)^2=Real.pi*(n+1:ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt Real.pi_pos.le]
    ring
  simp only [he,seriesKernel,neg_mul]
lemma dirichlet_series_fourier (T h x : ℝ) (hh : 0<h) :
    (∑' n : Nat, dirichletTerm T h x n)=∫ y : ℝ, psiKernel T h x y := by
  simp_rw [dirichlet_term_eq T h x hh]
  exact sum_kernel_integral T h x hh
noncomputable def positiveKernel (T h x y : ℝ) : ℂ :=
  Complex.exp ((y/4:ℝ):ℂ)*Q T h x y
noncomputable def negativeKernel (T h x y : ℝ) : ℂ :=
  Complex.exp ((-y/4:ℝ):ℂ)*Q T h x y
lemma positive_kernel_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (positiveKernel T h x) := by
  convert weighted_Q_integrable (1/4) T h x hh using 1
  ext y
  simp only [positiveKernel,one_div_mul_eq_div]
lemma negative_kernel_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (negativeKernel T h x) := by
  convert weighted_Q_integrable (-1/4) T h x hh using 1
  ext y
  unfold negativeKernel
  congr 2
  congr 1
  ring
lemma theta_kernel_eq (T h x : ℝ) :
    (fun y : ℝ => (P.f_modif (Real.exp y)*Complex.exp ((y/4:ℝ):ℂ)/2)*Q T h x y)
      =ᵐ[volume] (fun y : ℝ => psiKernel T h x y+
        (Iio (0:ℝ)).indicator (fun y => (positiveKernel T h x y-negativeKernel T h x y)/2) y) := by
  have hae : ∀ᵐ y : ℝ ∂volume, y≠0 := by
    rw [ae_iff]
    simp
  filter_upwards [hae] with y hy
  rcases lt_or_gt_of_ne hy with hn|hp
  · rw [Set.indicator_of_mem (show y∈Iio (0:ℝ) from hn),modif_lt_one _ (Real.exp_pos _) (by simpa using hn)]
    have he : Real.exp y^(-(1:ℝ)/2)=Real.exp (-y/2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      ring
    rw [he]
    unfold psiKernel positiveKernel negativeKernel psi
    push_cast
    have hm : (Real.exp (-y/2):ℂ)*Complex.exp ((y/4:ℝ):ℂ)=
        Complex.exp ((-y/4:ℝ):ℂ) := by
      rw [Complex.ofReal_exp,←Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = (((HurwitzZeta.evenKernel 0 (Real.exp y):ℂ)-1)/2)*
          Complex.exp ((y/4:ℝ):ℂ)*Q T h x y+
          (Complex.exp ((y/4:ℝ):ℂ)*Q T h x y-
            ((Real.exp (-y/2):ℂ)*Complex.exp ((y/4:ℝ):ℂ))*Q T h x y)/2 := by
        simp only [Complex.ofReal_exp]
        push_cast
        ring
      _ = _ := by rw [hm];push_cast;rfl
  · rw [Set.indicator_of_notMem (by simpa using hp.le),modif_one_lt _ (by simpa using hp)]
    simp only [add_zero]
    unfold psiKernel psi
    push_cast
    ring
lemma entire_fourier_correction (T h x : ℝ) (hh : 0<h) :
    𝓕 (entireWindow T h) x=(∑' n : Nat, dirichletTerm T h x n)+
      ((∫ y : ℝ in Iio 0, positiveKernel T h x y)-
        (∫ y : ℝ in Iio 0, negativeKernel T h x y))/2 := by
  rw [entire_window_fourier T h x hh,integral_congr_ae (theta_kernel_eq T h x)]
  have hi : Integrable (fun y : ℝ => (positiveKernel T h x y-negativeKernel T h x y)/2) :=
    ((positive_kernel_integrable T h x hh).sub (negative_kernel_integrable T h x hh)).div_const (2:ℂ)
  rw [integral_add (psi_kernel_integrable T h x hh) (hi.indicator measurableSet_Iio),
    integral_indicator measurableSet_Iio,integral_div,
    integral_sub (positive_kernel_integrable T h x hh).integrableOn
      (negative_kernel_integrable T h x hh).integrableOn,
    ←dirichlet_series_fourier T h x hh]
noncomputable def fullWindow (T h t : ℝ) : ℂ :=
  completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*I)*window T h t
lemma full_window_eq (T h t : ℝ) :
    fullWindow T h t=entireWindow T h t-poleWindow 1 T h t-poleWindow (-1) T h t := by
  unfold fullWindow entireWindow poleWindow sline
  rw [completedRiemannZeta_eq]
  have hs : 1-(1/2+((t+T:ℝ):ℂ)*I)=1/2+(-1:ℂ)*I*((t+T:ℝ):ℂ) := by ring
  rw [hs]
  push_cast
  ring
end RHHighPlattFourier

set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighPlattFourier
open RHHighGammaFourier RHHighThetaFourier RHHighThetaGamma RHHighPoleFourier
noncomputable def modulate (f : ℝ→ℂ) (x t : ℝ) : ℂ :=
  f t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma entire_modulate_integrable (T h x : ℝ) (hh : 0<h) :
    Integrable (modulate (entireWindow T h) x) := by
  convert (theta_joint_integrable T h x hh).integral_prod_left using 1
  ext t
  simp only [thetaJoint,integral_mul_const,integral_div]
  rw [←completed_log_mellin]
  rfl
lemma pole_modulate_integrable (ε T h x : ℝ) (hh : 0<h) :
    Integrable (modulate (poleWindow ε T h) x) := by
  convert ((pole_joint_integrable ε T h x hh).integral_prod_left).const_mul (1/2:ℂ) using 1
  ext t
  simp only [poleJoint,integral_mul_const]
  rw [laplace_half _ (by rw [sline_re];norm_num)]
  unfold poleWindow modulate
  ring
lemma full_fourier_decomposition (T h x : ℝ) (hh : 0<h) :
    𝓕 (fullWindow T h) x=𝓕 (entireWindow T h) x-
      𝓕 (poleWindow 1 T h) x-𝓕 (poleWindow (-1) T h) x := by
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
  have he (t : ℝ) : Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)*fullWindow T h t=
      modulate (entireWindow T h) x t-modulate (poleWindow 1 T h) x t-
        modulate (poleWindow (-1) T h) x t := by
    rw [full_window_eq]
    unfold modulate
    ring
  simp_rw [he]
  have hisub : Integrable (fun t : ℝ => modulate (entireWindow T h) x t-modulate (poleWindow 1 T h) x t) :=
    (entire_modulate_integrable T h x hh).sub (pole_modulate_integrable 1 T h x hh)
  rw [integral_sub hisub
    (pole_modulate_integrable (-1) T h x hh),
    integral_sub (entire_modulate_integrable T h x hh) (pole_modulate_integrable 1 T h x hh)]
  simp only [modulate,mul_comm]
lemma pole_plus_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow 1 T h) x=(∫ y : ℝ in Iio 0, positiveKernel T h x y)/2 := by
  rw [pole_window_fourier 1 T h x hh]
  have he : (fun y : ℝ => Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-1*y))=
      (fun y : ℝ => positiveKernel T h x (-y)) := by
    ext y
    simp [positiveKernel]
  rw [he,integral_comp_neg_Ioi,neg_zero,integral_Iic_eq_integral_Iio]
  ring
lemma pole_minus_fourier (T h x : ℝ) (hh : 0<h) :
    𝓕 (poleWindow (-1) T h) x=(∫ y : ℝ in Ioi 0, negativeKernel T h x y)/2 := by
  rw [pole_window_fourier (-1) T h x hh]
  simp only [neg_neg,one_mul]
  change (1/2:ℂ)*(∫ y : ℝ in Ioi 0, negativeKernel T h x y)=_
  ring
lemma full_fourier_series (T h x : ℝ) (hh : 0<h) :
    𝓕 (fullWindow T h) x=(∑' n : Nat, dirichletTerm T h x n)-
      2*(Real.pi:ℂ)*Complex.exp (
        ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by
  rw [full_fourier_decomposition T h x hh,entire_fourier_correction T h x hh,
    pole_plus_fourier T h x hh,pole_minus_fourier T h x hh]
  have hi : (∫ y : ℝ in Iio 0, negativeKernel T h x y)+
      (∫ y : ℝ in Ioi 0, negativeKernel T h x y)=∫ y : ℝ, negativeKernel T h x y := by
    rw [←integral_Iic_eq_integral_Iio]
    exact intervalIntegral.integral_Iic_add_Ioi (negative_kernel_integrable T h x hh).integrableOn
      (negative_kernel_integrable T h x hh).integrableOn
  have hm := gaussian_pole_mass T h x hh
  change (1/2:ℂ)*(∫ y : ℝ, negativeKernel T h x y)=_ at hm
  rw [←hm,←hi]
  ring
lemma full_fourier_remainder_norm (T h x : ℝ) (hh : 0<h) :
    ‖𝓕 (fullWindow T h) x-(∑' n : Nat, dirichletTerm T h x n)‖=
      2*Real.pi*Real.exp (1/(8*h^2)-T^2/(2*h^2)-Real.pi*x) := by
  rw [full_fourier_series T h x hh]
  simp only [sub_sub_cancel_left,norm_neg,norm_mul,Complex.norm_exp,
    Complex.add_re,Complex.ofReal_re]
  simp
  rw [abs_of_pos Real.pi_pos]
  have he : ((T:ℂ)/(2*(h:ℂ)^2)).im=0 := by
    rw [show (T:ℂ)/(2*(h:ℂ)^2)=((T/(2*h^2):ℝ):ℂ) by push_cast;rfl]
    rfl
  rw [he,add_zero]
end RHHighPlattFourier

open scoped FourierTransform
 theorem solution :
  ∀ (T h x : ℝ), 0<h →
  let w : ℝ→ℂ := fun t => Complex.exp ((Real.pi*(t+T)/4-t^2/(2*h^2):ℝ):ℂ)
  let G : ℝ→ℂ := fun t => Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*Complex.I)*w t
  𝓕 (fun t : ℝ => completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*Complex.I)*w t) x =
    (∑' n : Nat, Complex.exp (-(1/2+Complex.I*(T:ℂ))*(Real.log ((n+1:ℝ)*Real.sqrt Real.pi):ℂ))*
      𝓕 G (x+Real.log ((n+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi)))-
    2*(Real.pi:ℂ)*Complex.exp (((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
      Complex.I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by
  intro T h x hh
  exact RHHighPlattFourier.full_fourier_series T h x hh
