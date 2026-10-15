-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_finite_dirichlet50000
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:23:41.00799+00:00
-- url     : https://prove2.me/submissions/ddea506c-e78c-4aa2-9e3b-83eed4b13e6f

import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_high_height_scaled_gamma_bound
namespace RHHighCertifiedFiniteDirichlet
namespace RHHighSamplingFunctions
export _root_.RHHighSamplingFunctions (chirpedSample gammaWindow moment sampleIndex sampleTime)
end RHHighSamplingFunctions
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter
open scoped Topology
namespace RHHighContour
lemma horizontal_shift (f : ℂ→ℂ) (α : ℝ) (hf : Differentiable ℂ f)
    (h0 : Integrable (fun x : ℝ => f (x:ℂ)))
    (hα : Integrable (fun x : ℝ => f ((x:ℂ)+(α:ℂ)*I)))
    (hv : Tendsto (fun R : ℝ => ∫ y : ℝ in 0..α, f ((R:ℂ)+(y:ℂ)*I)) atTop (𝓝 0))
    (hvneg : Tendsto (fun R : ℝ => ∫ y : ℝ in 0..α, f ((R:ℂ)+(y:ℂ)*I)) atBot (𝓝 0)) :
    (∫ x : ℝ, f (x:ℂ))=∫ x : ℝ, f ((x:ℂ)+(α:ℂ)*I) := by
  have ht0 := intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id
  have htα := intervalIntegral_tendsto_integral hα tendsto_neg_atTop_atBot tendsto_id
  have ht := (((ht0.sub htα).add (hv.const_mul I)).sub
    ((hvneg.comp tendsto_neg_atTop_atBot).const_mul I))
  have he (R : ℝ) :
      (∫ x : ℝ in -R..R, f (x:ℂ))-
        (∫ x : ℝ in -R..R, f ((x:ℂ)+(α:ℂ)*I))+
        I*(∫ y : ℝ in 0..α, f ((R:ℂ)+(y:ℂ)*I))-
        I*(∫ y : ℝ in 0..α, f (((-R:ℝ):ℂ)+(y:ℂ)*I))=0 := by
    have hr := integral_boundary_rect_eq_zero_of_differentiableOn f (-R:ℂ)
      ((R:ℂ)+(α:ℂ)*I) hf.differentiableOn
    simpa only [neg_re,neg_im,neg_zero,ofReal_zero,ofReal_re,ofReal_im,add_re,mul_re,I_re,mul_zero,
      mul_im,I_im,mul_one,sub_zero,add_zero,add_im,zero_add,ofReal_neg,
      zero_mul,smul_eq_mul] using hr
  have hz : Tendsto (fun R : ℝ =>
      (∫ x : ℝ in -R..R, f (x:ℂ))-
        (∫ x : ℝ in -R..R, f ((x:ℂ)+(α:ℂ)*I))+
        I*(∫ y : ℝ in 0..α, f ((R:ℂ)+(y:ℂ)*I))-
        I*(∫ y : ℝ in 0..α, f (((-R:ℝ):ℂ)+(y:ℂ)*I))) atTop (𝓝 0) := by
    simpa only [he] using (tendsto_const_nhds (x:=(0:ℂ)) (f:=atTop))
  have heq := tendsto_nhds_unique ht hz
  simpa using sub_eq_zero.mp (by simpa using heq)
end RHHighContour
end
section
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
  have him : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by
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
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
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
end
section
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
end
section
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
end
section
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
end
section
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
end
section
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
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace RHHighGammaRotation
open RHHighGammaFourier
noncomputable def kernel (T h x : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt (2*Real.pi):ℂ)*(h:ℂ)*Complex.exp (-Complex.exp z+z/4+
    ((Real.pi*T/4:ℝ):ℂ)+(h:ℂ)^2/2*
      (((Real.pi/4:ℝ):ℂ)+I*(z/2-((2*Real.pi*x:ℝ):ℂ)))^2+I*(T:ℂ)*z/2)
lemma kernel_real (T h x y : ℝ) :
    kernel T h x (y:ℂ)=Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y := by
  unfold kernel Q
  have he : -(Complex.exp (y:ℂ))+(y:ℂ)/4+((Real.pi*T/4:ℝ):ℂ)+
      (h:ℂ)^2/2*(((Real.pi/4:ℝ):ℂ)+I*((y:ℂ)/2-((2*Real.pi*x:ℝ):ℂ)))^2+I*(T:ℂ)*y/2=
      ((-Real.exp y+y/4:ℝ):ℂ)+(((Real.pi*T/4:ℝ):ℂ)+(h:ℂ)^2/2*
        (((Real.pi/4:ℝ):ℂ)+I*((y/2-2*Real.pi*x:ℝ):ℂ))^2+I*(T:ℂ)*y/2) := by
    rw [←Complex.ofReal_exp]
    push_cast
    ring
  rw [he,Complex.exp_add]
  ring
lemma kernel_norm (T h x y α : ℝ) (hh : 0<h) :
    ‖kernel T h x ((y:ℂ)+(α:ℂ)*I)‖=Real.sqrt (2*Real.pi)*h*
      Real.exp (-Real.exp y*Real.cos α+y/4+Real.pi*T/4+
        h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2) := by
  rw [kernel,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hh,Complex.norm_exp]
  congr 2
  norm_num [add_re,neg_re,div_re,mul_re,pow_two,ofReal_re,ofReal_im,I_re,I_im,
    mul_im,add_im,sub_re,sub_im,exp_re,zero_mul,mul_zero,zero_add,add_zero,
    sub_zero,mul_one,one_mul,div_im,neg_im]
  ring
noncomputable def majorant (T h x y : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi)*h*Real.exp (y/4+Real.pi*T/4+h^2*Real.pi^2/32-
    h^2/2*(y/2-2*Real.pi*x)^2)
lemma kernel_norm_le (T h x y α : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    ‖kernel T h x ((y:ℂ)+(α:ℂ)*I)‖ ≤ majorant T h x y := by
  rw [kernel_norm T h x y α hh]
  unfold majorant
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hc : 0≤Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hα'⟩
  have hs : (Real.pi/4-α/2)^2≤Real.pi^2/16 := by
    nlinarith [Real.pi_pos]
  have hn : 0≤Real.exp y*Real.cos α := mul_nonneg (Real.exp_pos _).le hc
  have ht : 0≤T*α := mul_nonneg hT hα
  nlinarith [sq_nonneg h,mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hs)]
lemma majorant_integrable (T h x : ℝ) (hh : 0<h) : Integrable (majorant T h x) := by
  convert (weighted_Q_integrable (1/4) T h x hh).norm using 1
  ext y
  rw [norm_mul,Complex.norm_exp,Complex.ofReal_re,Q_norm T h x y hh]
  unfold majorant
  symm
  calc
    _ = Real.sqrt (2*Real.pi)*h*(Real.exp (y/4)*
      Real.exp (Real.pi*T/4+h^2*Real.pi^2/32-h^2/2*(y/2-2*Real.pi*x)^2)) := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring
lemma negative_quadratic_limit (b c d : ℝ) (hb : b<0) :
    Tendsto (fun y : ℝ => Real.exp (b*y^2+c*y+d)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have ht : Tendsto (fun y : ℝ => ((-b)*y-c)*y-d) atTop atTop := by
    apply tendsto_atTop_add_const_right
    apply Tendsto.atTop_mul_atTop₀ _ tendsto_id
    apply tendsto_atTop_add_const_right
    exact (tendsto_const_mul_atTop_of_pos (by linarith : 0 < -b)).mpr tendsto_id
  convert tendsto_neg_atTop_atBot.comp ht using 1
  ext y
  dsimp
  ring
end RHHighGammaRotation
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform
namespace RHHighGammaRotation
open RHHighGammaFourier RHHighContour
lemma majorant_limits (T h x : ℝ) (hh : 0<h) :
    Tendsto (majorant T h x) atTop (𝓝 0) ∧ Tendsto (majorant T h x) atBot (𝓝 0) := by
  let b : ℝ := -h^2/8
  let c : ℝ := h^2*Real.pi*x+1/4
  let d : ℝ := Real.pi*T/4+h^2*Real.pi^2/32-2*h^2*Real.pi^2*x^2
  have hb : b<0 := by dsimp [b];nlinarith [sq_pos_of_pos hh]
  have he (y : ℝ) : majorant T h x y=Real.sqrt (2*Real.pi)*h*Real.exp (b*y^2+c*y+d) := by
    unfold majorant
    congr 2
    dsimp [b,c,d]
    ring
  constructor
  · simpa only [←he,mul_zero] using (negative_quadratic_limit b c d hb).const_mul (Real.sqrt (2*Real.pi)*h)
  · have ht := (negative_quadratic_limit b (-c) d hb).comp tendsto_neg_atBot_atTop
    have he' : (fun y : ℝ => Real.exp (b*(-y)^2+(-c)*(-y)+d))=
        (fun y : ℝ => Real.exp (b*y^2+c*y+d)) := by ext y;congr 1;ring
    simp only [Function.comp_def] at ht
    rw [he'] at ht
    simpa only [←he,mul_zero] using ht.const_mul (Real.sqrt (2*Real.pi)*h)
lemma kernel_line_integrable (T h x α : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    Integrable (fun y : ℝ => kernel T h x ((y:ℂ)+(α:ℂ)*I)) := by
  apply (majorant_integrable T h x hh).mono'
  · have hc : Continuous (fun y : ℝ => kernel T h x ((y:ℂ)+(α:ℂ)*I)) := by unfold kernel;fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with y
    exact kernel_norm_le T h x y α hT hh hα hα'
lemma kernel_vertical_bound (T h x α R : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    ‖∫ y : ℝ in 0..α, kernel T h x ((R:ℂ)+(y:ℂ)*I)‖ ≤ majorant T h x R*α := by
  simpa only [sub_zero,abs_of_nonneg hα] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=α) (fun y hy =>
      kernel_norm_le T h x R y hT hh
        (by
          have hy' : y∈Ioc 0 α := by simpa only [uIoc_of_le hα] using hy
          exact hy'.1.le)
        (by
          have hy' : y∈Ioc 0 α := by simpa only [uIoc_of_le hα] using hy
          exact hy'.2.trans hα')))
lemma kernel_vertical_limits (T h x α : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in 0..α, kernel T h x ((R:ℂ)+(y:ℂ)*I)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ => ∫ y : ℝ in 0..α, kernel T h x ((R:ℂ)+(y:ℂ)*I)) atBot (𝓝 0) := by
  have hb (R : ℝ) := kernel_vertical_bound T h x α R hT hh hα hα'
  have hl := majorant_limits T h x hh
  constructor
  all_goals
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    · first | simpa using hl.1.mul_const α | simpa using hl.2.mul_const α
    · exact Eventually.of_forall (fun R => norm_nonneg _)
    · exact Eventually.of_forall hb
lemma gamma_contour_rotation (T h x α : ℝ) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α≤Real.pi/2) :
    𝓕 (gammaWindow T h) x=∫ y : ℝ, kernel T h x ((y:ℂ)+(α:ℂ)*I) := by
  rw [gamma_window_fourier T h x hh]
  have he : (fun y : ℝ => Complex.exp ((-Real.exp y+y/4:ℝ):ℂ)*Q T h x y)=
      (fun y : ℝ => kernel T h x (y:ℂ)) := by ext y;rw [kernel_real]
  rw [he]
  have hd : Differentiable ℂ (kernel T h x) := by unfold kernel;fun_prop
  have hz := kernel_line_integrable T h x 0 hT hh (by norm_num) (by positivity)
  have h0 : Integrable (fun y : ℝ => kernel T h x (y:ℂ)) := by simpa using hz
  exact horizontal_shift _ α hd h0 (kernel_line_integrable T h x α hT hh hα hα')
    (kernel_vertical_limits T h x α hT hh hα hα').1
    (kernel_vertical_limits T h x α hT hh hα hα').2
end RHHighGammaRotation
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaRotation
open RHHighGammaFourier
lemma integral_real_quadratic (b c d : ℝ) (hb : b<0) :
    (∫ y : ℝ, Real.exp (b*y^2+c*y+d))=
      Real.sqrt (Real.pi/(-b))*Real.exp (d-c^2/(4*b)) := by
  have he (y : ℝ) : b*y^2+c*y+d=b*(y+c/(2*b))^2+(d-c^2/(4*b)) := by
    field_simp [hb.ne]
    ring
  simp_rw [he,Real.exp_add]
  rw [integral_mul_const,integral_add_right_eq_self (μ:=(volume:Measure ℝ))
    (fun y : ℝ => Real.exp (b*y^2)) (c/(2*b))]
  have hg : (fun y : ℝ => Real.exp (b*y^2))=(fun y : ℝ => Real.exp (-(-b)*y^2)) := by
    ext y
    simp
  rw [hg,integral_gaussian]
lemma gaussian_prefactor (h : ℝ) (hh : 0<h) :
    Real.sqrt (2*Real.pi)*h*Real.sqrt (Real.pi/(h^2/8))=4*Real.pi := by
  have he : Real.pi/(h^2/8)=8*Real.pi/h^2 := by ring
  rw [he,Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hh]
  have hs : Real.sqrt (8*Real.pi)=2*Real.sqrt (2*Real.pi) := by
    rw [show 8*Real.pi=4*(2*Real.pi) by ring,Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt 4=2 by norm_num]
  rw [hs]
  calc
    _ = 2*(Real.sqrt (2*Real.pi))^2 := by field_simp [hh.ne'] <;> ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)];ring
lemma kernel_half_pi_mass (T h x : ℝ) (hh : 0<h) :
    (∫ y : ℝ, ‖kernel T h x ((y:ℂ)+((Real.pi/2:ℝ):ℂ)*I)‖)=
      4*Real.pi*Real.exp (Real.pi*x+1/(8*h^2)) := by
  simp_rw [kernel_norm T h x _ _ hh,Real.cos_pi_div_two]
  have he (y : ℝ) : -Real.exp y*0+y/4+Real.pi*T/4+
      h^2/2*((Real.pi/4-(Real.pi/2)/2)^2-(y/2-2*Real.pi*x)^2)-T*(Real.pi/2)/2=
      (-h^2/8)*y^2+(h^2*Real.pi*x+1/4)*y-2*h^2*Real.pi^2*x^2 := by ring
  simp_rw [he]
  rw [integral_const_mul]
  simp only [sub_eq_add_neg]
  rw [integral_real_quadratic _ _ _ (by nlinarith [sq_pos_of_pos hh])]
  have hb : -(-h^2/8)=h^2/8 := by ring
  rw [hb,←mul_assoc,gaussian_prefactor h hh]
  congr 2
  field_simp [hh.ne']
  ring
lemma gamma_fourier_negative_bound (T h x : ℝ) (hT : 0≤T) (hh : 0<h) :
    ‖𝓕 (gammaWindow T h) x‖ ≤ 4*Real.pi*Real.exp (Real.pi*x+1/(8*h^2)) := by
  rw [gamma_contour_rotation T h x (Real.pi/2) hT hh (by positivity) le_rfl]
  exact (norm_integral_le_integral_norm _).trans_eq (kernel_half_pi_mass T h x hh)
end RHHighGammaRotation
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaComplexFourier
open RHHighGammaFourier RHHighGammaRotation
noncomputable def transform (T h : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, gammaWindow T h t*Complex.exp (-2*(Real.pi:ℂ)*I*z*t)
lemma transform_real (T h x : ℝ) : transform T h (x:ℂ)=𝓕 (gammaWindow T h) x := by
  rw [transform,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul]
  have he : -2*(Real.pi:ℂ)*I*(x:ℂ)*t=(((-2*Real.pi*t*x:ℝ):ℂ)*I) := by push_cast;ring
  rw [he,mul_comm]
lemma transform_complex_shift (T h x v : ℝ) (hh : 0<h) :
    transform T h ((x:ℂ)+(v:ℂ)*I)=
      Complex.exp (((2*Real.pi^2*h^2*v^2:ℝ):ℂ)-
        I*((4*Real.pi^2*h^2*x*v:ℝ):ℂ))*
          𝓕 (gammaWindow (T+2*Real.pi*h^2*v) h) x := by
  let m : ℝ := 2*Real.pi*h^2*v
  rw [transform]
  rw [←integral_add_right_eq_self (μ:=(volume:Measure ℝ))
    (fun t : ℝ => gammaWindow T h t*Complex.exp (-2*(Real.pi:ℂ)*I*((x:ℂ)+(v:ℂ)*I)*t)) m]
  rw [Real.fourier_real_eq_integral_exp_smul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul]
  unfold gammaWindow window
  have harg : (((t+m+T)/2:ℝ):ℂ)=(((t+(T+2*Real.pi*h^2*v))/2:ℝ):ℂ) := by
    dsimp [m]
    congr 1
    ring
  rw [harg]
  have he : ((Real.pi*(t+m+T)/4-(t+m)^2/(2*h^2):ℝ):ℂ)+
      (-2*(Real.pi:ℂ)*I*((x:ℂ)+(v:ℂ)*I)*(t+m))=
      (((2*Real.pi^2*h^2*v^2:ℝ):ℂ)-I*((4*Real.pi^2*h^2*x*v:ℝ):ℂ))+
        (((-2*Real.pi*t*x:ℝ):ℂ)*I)+
        ((Real.pi*(t+(T+2*Real.pi*h^2*v))/4-t^2/(2*h^2):ℝ):ℂ) := by
    dsimp [m]
    push_cast
    have hn : (h:ℂ)≠0 := by exact_mod_cast hh.ne'
    field_simp [hn]
    ring_nf <;> simp only [Complex.I_sq] <;> ring
  calc
    _ = Complex.Gamma (1/4+(((t+(T+2*Real.pi*h^2*v))/2:ℝ):ℂ)*I)*
      Complex.exp (((Real.pi*(t+m+T)/4-(t+m)^2/(2*h^2):ℝ):ℂ)+
        (-2*(Real.pi:ℂ)*I*((x:ℂ)+(v:ℂ)*I)*(t+m))) := by rw [Complex.exp_add];push_cast;ring
    _ = _ := by rw [he,Complex.exp_add,Complex.exp_add];push_cast;ring
lemma transform_complex_negative_bound (T h x v : ℝ) (hh : 0<h)
    (hT : 0≤T+2*Real.pi*h^2*v) :
    ‖transform T h ((x:ℂ)+(v:ℂ)*I)‖ ≤
      4*Real.pi*Real.exp (Real.pi*x+1/(8*h^2)+2*Real.pi^2*h^2*v^2) := by
  rw [transform_complex_shift T h x v hh,norm_mul,Complex.norm_exp]
  have he : ((((2*Real.pi^2*h^2*v^2:ℝ):ℂ)-I*((4*Real.pi^2*h^2*x*v:ℝ):ℂ))).re=
      2*Real.pi^2*h^2*v^2 := by
    simp only [sub_re,ofReal_re,mul_re,mul_im,I_re,I_im,ofReal_im,mul_zero,
      zero_mul,zero_add,sub_zero]
  rw [he]
  have hb := mul_le_mul_of_nonneg_left
    (gamma_fourier_negative_bound (T+2*Real.pi*h^2*v) h x hT hh)
    (Real.exp_pos (2*Real.pi^2*h^2*v^2)).le
  apply hb.trans_eq
  calc
    _ = 4*Real.pi*(Real.exp (2*Real.pi^2*h^2*v^2)*Real.exp (Real.pi*x+1/(8*h^2))) := by ring
    _ = _ := by rw [←Real.exp_add];congr 2;ring
end RHHighGammaComplexFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex CauSeq Finset
namespace RHHighTaylor
lemma exp_factorial_remainder (z : ℂ) (n : Nat) :
    ‖Complex.exp z-∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)‖≤
      (‖z‖^n/(n.factorial:ℝ))*Real.exp ‖z‖ := by
  rw [←CauSeq.lim_const (abv:=norm) (∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)),
    Complex.exp,sub_eq_add_neg,←CauSeq.lim_neg]
  rw [CauSeq.lim_add (Complex.exp' z) (-CauSeq.const norm (∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ))),
    ←Complex.lim_norm]
  refine CauSeq.lim_le (CauSeq.le_of_exists ⟨n,fun j hj => ?_⟩)
  simp_rw [←sub_eq_add_neg]
  change ‖(∑ k ∈ Finset.range j, z^k/(k.factorial:ℂ))-
    ∑ k ∈ Finset.range n, z^k/(k.factorial:ℂ)‖≤_
  let m := j-n
  have he : j=n+m := (Nat.add_sub_of_le hj).symm
  rw [he,Finset.sum_range_add_sub_sum_range]
  calc
    _ ≤ ∑ k ∈ Finset.range m, ‖z^(n+k)/((n+k).factorial:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, (‖z‖^n/(n.factorial:ℝ))*(‖z‖^k/(k.factorial:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [norm_div,Complex.norm_pow,norm_natCast,pow_add,norm_mul]
      rw [div_mul_div_comm]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n k)
    _ = (‖z‖^n/(n.factorial:ℝ))*(∑ k ∈ Finset.range m, ‖z‖^k/(k.factorial:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (norm_nonneg z) m) (by positivity)
end RHHighTaylor
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGaussianTaylor
open RHHighGammaFourier RHHighTaylor
lemma gamma_window_norm (T h t : ℝ) : ‖gammaWindow T h t‖≤6*Real.exp (-t^2/(2*h^2)) := by
  have h := TaoFivePrimes.rh_high_height_scaled_gamma_bound.2 T t h 0
  simpa only [pow_zero,mul_one,one_mul,gammaWindow,window,Complex.ofReal_exp] using h
lemma pow_exp_factorial (v : ℝ) (hv : 0≤v) (n : Nat) :
    v^n*Real.exp (-v)≤(n.factorial:ℝ) := by
  have hp := Real.pow_div_factorial_le_exp v hv n
  rw [div_le_iff₀ (show (0:ℝ)<n.factorial by positivity)] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-v)).le
  have he : Real.exp v*(n.factorial:ℝ)*Real.exp (-v)=(n.factorial:ℝ) := by
    calc
      _ = n.factorial*(Real.exp v*Real.exp (-v)) := by ring
      _ = _ := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  simpa only [he] using hm
lemma young_gaussian (t : ℝ) :
    Real.exp (-t^2/800+|t|/128)≤3*Real.exp (-t^2/1600) := by
  have hy : -t^2/800+|t|/128≤1-t^2/1600 := by
    nlinarith [sq_abs t,sq_nonneg (|t|-25/4)]
  calc
    _ ≤ Real.exp (1-t^2/1600) := Real.exp_le_exp.mpr hy
    _ = Real.exp 1*Real.exp (-t^2/1600) := by rw [sub_eq_add_neg,Real.exp_add,neg_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le
lemma polynomial_gaussian (t : ℝ) :
    |t|^20*Real.exp (-t^2/1600)≤
      (3200:ℝ)^10*((10).factorial:ℝ)*Real.exp (-t^2/3200) := by
  have hp := pow_exp_factorial (t^2/3200) (by positivity) 10
  have he : |t|^20=(3200:ℝ)^10*(t^2/3200)^10 := by
    rw [show (20:Nat)=2*10 by norm_num,pow_mul,sq_abs]
    ring
  have he' : -t^2/1600= -t^2/3200+(-t^2/3200) := by ring
  rw [he,he',Real.exp_add]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hp (Real.exp_pos (-t^2/3200)).le)
    (show 0≤(3200:ℝ)^10 by positivity)
  convert hm using 1 <;> first | rfl | ring
noncomputable def remainder (T δ t : ℝ) : ℂ :=
  gammaWindow T 20 t*(Complex.exp (-2*(Real.pi:ℂ)*I*(δ:ℂ)*t)-
    ∑ k ∈ Finset.range 20, (-2*(Real.pi:ℂ)*I*(δ:ℂ)*t)^k/(k.factorial:ℂ))
noncomputable def constant : ℝ :=
  18*(1/128:ℝ)^20*(3200:ℝ)^10*((10).factorial:ℝ)/((20).factorial:ℝ)
lemma remainder_norm (T δ t : ℝ) (hδ : |δ|≤1/1024) :
    ‖remainder T δ t‖ ≤ constant*Real.exp (-t^2/3200) := by
  let z : ℂ := -2*(Real.pi:ℂ)*I*(δ:ℂ)*t
  have hn : ‖z‖≤|t|/128 := by
    dsimp [z]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,norm_neg,
      norm_ofNat,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_lt_four,Real.pi_pos,abs_nonneg δ,abs_nonneg t,
      mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hδ),
      mul_nonneg (abs_nonneg δ) (sub_nonneg.mpr Real.pi_lt_four.le)]
  have hg := gamma_window_norm T 20 t
  norm_num at hg
  have hr := exp_factorial_remainder z 20
  have hz : ‖remainder T δ t‖=‖gammaWindow T 20 t‖*
      ‖Complex.exp z-∑ k ∈ Finset.range 20, z^k/(k.factorial:ℂ)‖ := by rw [remainder,norm_mul]
  rw [hz]
  calc
    _ ≤ (6*Real.exp (-t^2/800))*((|t|/128)^20/((20).factorial:ℝ)*Real.exp (|t|/128)) := by
      apply mul_le_mul hg _ (norm_nonneg _) (by positivity)
      apply hr.trans
      gcongr
    _ = (6*(1/128:ℝ)^20/((20).factorial:ℝ))*|t|^20*
        Real.exp (-t^2/800+|t|/128) := by rw [Real.exp_add];ring
    _ ≤ (18*(1/128:ℝ)^20/((20).factorial:ℝ))*(|t|^20*Real.exp (-t^2/1600)) := by
      have hm := mul_le_mul_of_nonneg_left (young_gaussian t)
        (show 0≤(6*(1/128:ℝ)^20/((20).factorial:ℝ))*|t|^20 by positivity)
      convert hm using 1 <;> first | rfl | ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left (polynomial_gaussian t)
        (show 0≤18*(1/128:ℝ)^20/((20).factorial:ℝ) by positivity)
      convert hm using 1 <;> first | rfl | (simp only [constant];ring)
end RHHighGaussianTaylor
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
namespace RHHighGaussianTaylor
open RHHighGammaFourier
lemma gamma_window_continuous (T h : ℝ) : Continuous (gammaWindow T h) := by
  have hc : Continuous (fun t : ℝ => Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    · intro m hm
      have hz : 0<(1/4+(((t+T)/2:ℝ):ℂ)*I).re := by simp
      rw [hm] at hz
      have hmr : (0:ℝ) ≤ m := by positivity
      simp only [neg_re,natCast_re] at hz
      linarith
  have hw : Continuous (window T h) := by unfold window;fun_prop
  exact hc.mul hw
lemma remainder_continuous (T δ : ℝ) : Continuous (remainder T δ) := by
  have hg := gamma_window_continuous T 20
  unfold remainder
  apply hg.mul
  fun_prop
lemma gaussian_bound_integrable : Integrable (fun t : ℝ => Real.exp (-t^2/3200)) := by
  convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/3200) using 1
  ext t
  congr 1
  ring
lemma remainder_integrable (T δ : ℝ) (hδ : |δ|≤1/1024) : Integrable (remainder T δ) := by
  apply (gaussian_bound_integrable.const_mul constant).mono' (remainder_continuous T δ).aestronglyMeasurable
  filter_upwards [] with t
  exact remainder_norm T δ t hδ
lemma gaussian_mass_le : (∫ t : ℝ, Real.exp (-t^2/3200))≤120 := by
  have he : (fun t : ℝ => Real.exp (-t^2/3200))=(fun t : ℝ => Real.exp (-(1/3200:ℝ)*t^2)) := by
    ext t
    congr 1
    ring
  rw [he,integral_gaussian]
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · norm_num
    nlinarith [Real.pi_lt_four]
lemma constant_mass_small : constant*120≤1/10^15 := by
  norm_num [constant,Nat.factorial]
lemma modulated_remainder_integral (T δ x : ℝ) (hδ : |δ|≤1/1024) :
    ‖∫ t : ℝ, remainder T δ t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)‖≤1/10^15 := by
  have hc : 0≤constant := by unfold constant;positivity
  have hb : ∀ᵐ t : ℝ ∂volume,
      ‖remainder T δ t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)‖≤constant*Real.exp (-t^2/3200) := by
    filter_upwards [] with t
    rw [norm_mul,Complex.norm_exp]
    have he : (((-2*Real.pi*t*x:ℝ):ℂ)*I).re=0 := by simp
    rw [he,Real.exp_zero,mul_one]
    exact remainder_norm T δ t hδ
  calc
    _ ≤ ∫ t : ℝ, constant*Real.exp (-t^2/3200) :=
      norm_integral_le_of_norm_le (gaussian_bound_integrable.const_mul constant) hb
    _ = constant*(∫ t : ℝ, Real.exp (-t^2/3200)) := integral_const_mul _ _
    _ ≤ constant*120 := mul_le_mul_of_nonneg_left gaussian_mass_le hc
    _ ≤ _ := constant_mass_small
end RHHighGaussianTaylor
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaTaylorFourier
open RHHighGammaFourier RHHighGaussianTaylor
noncomputable def phase (x t : ℝ) : ℂ := Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I)
lemma phase_norm (x t : ℝ) : ‖phase x t‖=1 := by simp [phase,Complex.norm_exp]
lemma modulate_integrable (f : ℝ→ℂ) (hf : Integrable f) (x : ℝ) :
    Integrable (fun t : ℝ => f t*phase x t) := by
  apply hf.norm.mono'
  · have hc : Continuous (phase x) := by unfold phase;fun_prop
    exact hf.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul,phase_norm,mul_one]
lemma fourier_eq (f : ℝ→ℂ) (x : ℝ) : 𝓕 f x=∫ t : ℝ, f t*phase x t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul,phase,mul_comm]
noncomputable def moment (T : ℝ) (k : Nat) (t : ℝ) : ℂ :=
  gammaWindow T 20 t*(-2*(Real.pi:ℂ)*I*(t:ℂ))^k
lemma moment_integrable (T : ℝ) (k : Nat) : Integrable (moment T k) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (b:=(1/800:ℝ)) (by norm_num)
    (s:=(k:ℝ)) (by
      have hk : (0:ℝ)≤k := by positivity
      linarith)
  have hi' : Integrable (fun t : ℝ => |t|^k*Real.exp (-t^2/800)) := by
    convert hi.norm using 1
    ext t
    rw [Real.norm_eq_abs,abs_mul,Real.rpow_natCast,abs_pow,abs_of_pos (Real.exp_pos _)]
    congr 2
    ring
  have hc : Continuous (moment T k) := by
    have hg := gamma_window_continuous T 20
    unfold moment
    fun_prop
  apply (hi'.const_mul (6*(2*Real.pi)^k)).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.2 T t 20 k
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num] at hg
  simpa only [moment,gammaWindow,window,show (2*(20:ℝ)^2)=800 by norm_num,
    Complex.ofReal_exp,mul_pow,mul_assoc] using hg
noncomputable def polynomial (T δ t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range 20, ((δ:ℂ)^k/(k.factorial:ℂ))*moment T k t
lemma polynomial_integrable (T δ : ℝ) : Integrable (polynomial T δ) := by
  exact integrable_finsetSum _ (fun k hk => (moment_integrable T k).const_mul _)
lemma remainder_eq (T δ t : ℝ) :
    remainder T δ t=gammaWindow T 20 t*phase δ t-polynomial T δ t := by
  unfold remainder phase polynomial moment
  rw [mul_sub,Finset.mul_sum]
  congr 1
  · congr 2
    push_cast
    ring
  · apply Finset.sum_congr rfl
    intro k hk
    have he : -2*(Real.pi:ℂ)*I*(δ:ℂ)*t=(δ:ℂ)*(-2*(Real.pi:ℂ)*I*(t:ℂ)) := by ring
    rw [he,mul_pow]
    ring
lemma shifted_fourier (T δ x : ℝ) :
    𝓕 (gammaWindow T 20) (x+δ)=𝓕 (fun t : ℝ => gammaWindow T 20 t*phase δ t) x := by
  rw [fourier_eq,fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold phase
  conv_rhs => rw [mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring
lemma polynomial_fourier (T δ x : ℝ) :
    𝓕 (polynomial T δ) x=
      ∑ k ∈ Finset.range 20, ((δ:ℂ)^k/(k.factorial:ℂ))*𝓕 (moment T k) x := by
  rw [fourier_eq]
  simp only [polynomial,Finset.sum_mul]
  simp only [mul_assoc]
  rw [integral_finsetSum _ (fun k hk =>
    (modulate_integrable (moment T k) (moment_integrable T k) x).const_mul _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_eq,←integral_const_mul]
lemma fourier_taylor_error (T δ x : ℝ) (hδ : |δ|≤1/1024) :
    ‖𝓕 (gammaWindow T 20) (x+δ)-
      ∑ k ∈ Finset.range 20, ((δ:ℂ)^k/(k.factorial:ℂ))*𝓕 (moment T k) x‖≤1/10^15 := by
  have hg : Integrable (gammaWindow T 20) := by
    convert moment_integrable T 0 using 1
    ext t
    simp [moment]
  rw [shifted_fourier,←polynomial_fourier,fourier_eq,fourier_eq]
  rw [←integral_sub (modulate_integrable _ (modulate_integrable _ hg δ) x)
    (modulate_integrable _ (polynomial_integrable T δ) x)]
  have he : (fun t : ℝ => (gammaWindow T 20 t*phase δ t)*phase x t-polynomial T δ t*phase x t)=
      (fun t : ℝ => remainder T δ t*phase x t) := by
    ext t
    rw [remainder_eq]
    ring
  rw [he]
  exact modulated_remainder_integral T δ x hδ
end RHHighGammaTaylorFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHHighGammaCircle
open RHHighGammaFourier RHHighGammaComplexFourier RHHighGammaTaylorFourier RHHighGaussianTaylor
noncomputable def joint (T x r : ℝ) (k : Nat) (θ t : ℝ) : ℂ :=
  (deriv (circleMap (x:ℂ) r) θ/((circleMap (x:ℂ) r θ-(x:ℂ))^(k+1)))*
    gammaWindow T 20 t*Complex.exp (-2*(Real.pi:ℂ)*I*(circleMap (x:ℂ) r θ)*t)
lemma circle_sub_norm (x r θ : ℝ) (hr : 0<r) :
    ‖circleMap (x:ℂ) r θ-(x:ℂ)‖=r := by
  rw [circleMap_sub_center,norm_circleMap_zero,abs_of_pos hr]
lemma circle_sub_ne (x r θ : ℝ) (hr : 0<r) :
    circleMap (x:ℂ) r θ-(x:ℂ)≠0 := by
  apply norm_pos_iff.mp
  rw [circle_sub_norm x r θ hr]
  exact hr
lemma circle_im_le (x r θ : ℝ) (hr : 0<r) : |(circleMap (x:ℂ) r θ).im|≤r := by
  have h := Complex.abs_im_le_norm (circleMap (x:ℂ) r θ-(x:ℂ))
  simpa only [sub_im,ofReal_im,sub_zero,circle_sub_norm x r θ hr] using h
lemma joint_norm_le (T x r θ t : ℝ) (k : Nat) (hr : 0<r) :
    ‖joint T x r k θ t‖ ≤
      ((6/r^k)*Real.exp (1600*Real.pi^2*r^2))*Real.exp (-t^2/1600) := by
  rw [joint,norm_mul,norm_mul,norm_div,deriv_circleMap,norm_mul,norm_I,mul_one,
    norm_circleMap_zero,abs_of_pos hr,norm_pow,circle_sub_norm x r θ hr,Complex.norm_exp]
  have he : (-2*(Real.pi:ℂ)*I*(circleMap (x:ℂ) r θ)*t).re=
      2*Real.pi*(circleMap (x:ℂ) r θ).im*t := by
    simp only [mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im,mul_zero,zero_mul,
      mul_one,one_mul,sub_zero,zero_sub,neg_re,neg_im]
    norm_num
  rw [he]
  have hph : 2*Real.pi*(circleMap (x:ℂ) r θ).im*t≤2*Real.pi*r*|t| := by
    have hi := circle_im_le x r θ hr
    have hab := le_abs_self ((circleMap (x:ℂ) r θ).im*t)
    rw [abs_mul] at hab
    have hm := mul_le_mul_of_nonneg_right hi (abs_nonneg t)
    nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left (hab.trans hm) Real.pi_pos.le]
  have hy : -t^2/800+2*Real.pi*r*|t|≤1600*Real.pi^2*r^2-t^2/1600 := by
    nlinarith [sq_abs t,sq_nonneg (|t|-1600*Real.pi*r)]
  have hg := gamma_window_norm T 20 t
  norm_num at hg
  have hquot : r/r^(k+1)=1/r^k := by rw [pow_succ];field_simp [hr.ne']
  rw [hquot]
  calc
    _ ≤ (1/r^k)*(6*Real.exp (-t^2/800))*Real.exp (2*Real.pi*r*|t|) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity))
        (Real.exp_le_exp.mpr hph) (Real.exp_pos _).le (by positivity)
    _ = (6/r^k)*Real.exp (-t^2/800+2*Real.pi*r*|t|) := by rw [Real.exp_add];ring
    _ ≤ (6/r^k)*Real.exp (1600*Real.pi^2*r^2-t^2/1600) := by gcongr
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add,neg_div];ring
lemma joint_continuous (T x r : ℝ) (k : Nat) (hr : 0<r) :
    Continuous (fun p : ℝ×ℝ => joint T x r k p.1 p.2) := by
  have hc : Continuous (fun θ : ℝ => deriv (circleMap (x:ℂ) r) θ/
      (circleMap (x:ℂ) r θ-(x:ℂ))^(k+1)) := by
    simp only [deriv_circleMap]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro θ
      exact pow_ne_zero _ (circle_sub_ne x r θ hr)
  have hg : Continuous (fun p : ℝ×ℝ => gammaWindow T 20 p.2) :=
    (gamma_window_continuous T 20).comp continuous_snd
  have he : Continuous (fun p : ℝ×ℝ => Complex.exp (-2*(Real.pi:ℂ)*I*(circleMap (x:ℂ) r p.1)*p.2)) := by fun_prop
  exact ((hc.comp continuous_fst).mul hg).mul he
lemma joint_integrable (T x r : ℝ) (k : Nat) (hr : 0<r) :
    Integrable (fun p : ℝ×ℝ => joint T x r k p.1 p.2)
      ((volume.restrict (Icc 0 (2*Real.pi))).prod volume) := by
  have hθ : IntegrableOn (fun θ : ℝ => (1:ℝ)) (Icc 0 (2*Real.pi)) :=
    continuous_const.integrableOn_Icc
  have ht : Integrable (fun t : ℝ => Real.exp (-t^2/1600)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/1600) using 1
    ext t
    congr 1
    ring
  have hm := hθ.mul_prod (ht.const_mul ((6/r^k)*Real.exp (1600*Real.pi^2*r^2)))
  apply hm.mono' (joint_continuous T x r k hr).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [one_mul] using joint_norm_le T x r p.1 p.2 k hr
end RHHighGammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHHighGammaCircle
open RHHighGammaFourier RHHighGammaComplexFourier RHHighGammaTaylorFourier RHHighGaussianTaylor
lemma circle_exp_coefficient (a c : ℂ) (r : ℝ) (hr : 0<r) (k : Nat) :
    (∮ z in C(c,r), (1/(z-c)^(k+1))*Complex.exp (a*z))=
      (2*(Real.pi:ℂ)*I/(k.factorial:ℂ))*(a^k*Complex.exp (a*c)) := by
  have hd : Differentiable ℂ (fun z : ℂ => Complex.exp (a*z)) := by fun_prop
  have h := hd.diffContOnCl.circleIntegral_one_div_sub_center_pow_smul (c:=c) hr k
  simpa only [smul_eq_mul,iteratedDeriv_cexp_const_mul] using h
lemma joint_inner (T x r t : ℝ) (k : Nat) (hr : 0<r) :
    (∫ θ : ℝ in Icc 0 (2*Real.pi), joint T x r k θ t)=
      (2*(Real.pi:ℂ)*I/(k.factorial:ℂ))*(moment T k t*phase x t) := by
  let a : ℂ := -2*(Real.pi:ℂ)*I*(t:ℂ)
  have he : (∫ θ : ℝ in Icc 0 (2*Real.pi), joint T x r k θ t)=
      ∮ z in C((x:ℂ),r), gammaWindow T 20 t*((1/(z-(x:ℂ))^(k+1))*Complex.exp (a*z)) := by
    rw [circleIntegral_def_Icc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    dsimp [joint]
    have hexp : -2*(Real.pi:ℂ)*I*(circleMap (x:ℂ) r θ)*t=a*(circleMap (x:ℂ) r θ) := by dsimp [a];ring
    rw [hexp]
    ring
  rw [he]
  have hm := circleIntegral.integral_smul (gammaWindow T 20 t)
    (fun z : ℂ => (1/(z-(x:ℂ))^(k+1))*Complex.exp (a*z)) (x:ℂ) r
  simp only [smul_eq_mul] at hm
  rw [hm,circle_exp_coefficient a (x:ℂ) r hr k]
  have hexp : a*(x:ℂ)=(((-2*Real.pi*t*x:ℝ):ℂ)*I) := by dsimp [a];push_cast;ring
  rw [hexp]
  unfold moment phase
  dsimp [a]
  ring
lemma circle_transform_eq (T x r : ℝ) (k : Nat) (hr : 0<r) :
    (∮ z in C((x:ℂ),r), (1/(z-(x:ℂ))^(k+1))*transform T 20 z)=
      (2*(Real.pi:ℂ)*I/(k.factorial:ℂ))*𝓕 (moment T k) x := by
  have he : (∮ z in C((x:ℂ),r), (1/(z-(x:ℂ))^(k+1))*transform T 20 z)=
      ∫ θ : ℝ in Icc 0 (2*Real.pi), ∫ t : ℝ, joint T x r k θ t := by
    rw [circleIntegral_def_Icc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ hθ
    unfold transform
    simp only [joint,smul_eq_mul,mul_assoc,integral_const_mul]
    ring
  rw [he,integral_integral_swap (joint_integrable T x r k hr)]
  simp_rw [joint_inner T x r _ k hr]
  rw [integral_const_mul,fourier_eq]
lemma moment_fourier_cauchy (T x r M : ℝ) (k : Nat) (hr : 0<r)
    (hM : ∀ z ∈ sphere (x:ℂ) r, ‖transform T 20 z‖≤M) :
    ‖𝓕 (moment T k) x‖/(k.factorial:ℝ)≤M/r^k := by
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f:=fun z : ℂ => (1/(z-(x:ℂ))^(k+1))*transform T 20 z) hr.le
    (C:=M/r^(k+1)) (fun z hz => by
      rw [norm_mul,norm_div,norm_one,norm_pow,(mem_sphere_iff_norm.mp hz)]
      exact (mul_le_mul_of_nonneg_left (hM z hz) (by positivity)).trans_eq (by ring))
  rw [circle_transform_eq T x r k hr,smul_eq_mul] at hb
  have he : (2*(Real.pi:ℂ)*I)⁻¹*((2*(Real.pi:ℂ)*I/(k.factorial:ℂ))*𝓕 (moment T k) x)=
      𝓕 (moment T k) x/(k.factorial:ℂ) := by
    field_simp [Real.pi_ne_zero,Complex.I_ne_zero,show (k.factorial:ℂ)≠0 by exact_mod_cast k.factorial_ne_zero]
  rw [he,norm_div,norm_natCast] at hb
  have hpow : r*(M/r^(k+1))=M/r^k := by rw [pow_succ];field_simp [hr.ne'] <;> ring
  simpa only [hpow] using hb
end RHHighGammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHHighGammaCircle
open RHHighGammaFourier RHHighGammaComplexFourier RHHighGammaTaylorFourier
noncomputable def radius : ℝ := 1/(40*Real.pi)
lemma radius_pos : 0<radius := by unfold radius;positivity
lemma radius_pi : Real.pi*radius=1/40 := by unfold radius;field_simp
lemma radius_quadratic : 800*Real.pi^2*radius^2=1/2 := by
  unfold radius
  field_simp
  ring
lemma transform_sphere_bound (T x : ℝ) (hT : 20≤T) :
    ∀ z ∈ sphere (x:ℂ) radius, ‖transform T 20 z‖≤12*Real.pi*Real.exp (Real.pi*x) := by
  intro z hz
  have hn : ‖z-(x:ℂ)‖=radius := mem_sphere_iff_norm.mp hz
  have hi : |z.im|≤radius := by
    simpa only [sub_im,ofReal_im,sub_zero,hn] using Complex.abs_im_le_norm (z-(x:ℂ))
  have hr : z.re≤x+radius := by
    have he := Complex.re_le_norm (z-(x:ℂ))
    simp only [sub_re,ofReal_re,hn] at he
    linarith
  have hv : 0≤T+2*Real.pi*(20:ℝ)^2*z.im := by
    have he := mul_le_mul_of_nonneg_left (abs_le.mp hi).1 (by positivity : 0≤800*Real.pi)
    have hp : 800*Real.pi*radius=20 := by rw [mul_assoc,radius_pi];norm_num
    nlinarith
  have hg := transform_complex_negative_bound T 20 z.re z.im (by norm_num) hv
  rw [Complex.re_add_im] at hg
  have he : Real.pi*z.re+1/(8*(20:ℝ)^2)+2*Real.pi^2*(20:ℝ)^2*z.im^2≤Real.pi*x+1 := by
    have hi2 : z.im^2≤radius^2 := by
      have hs := (sq_le_sq₀ (abs_nonneg z.im) radius_pos.le).mpr hi
      simpa only [sq_abs] using hs
    have hre := mul_le_mul_of_nonneg_left hr Real.pi_pos.le
    have hime := mul_le_mul_of_nonneg_left hi2 (by positivity : 0≤800*Real.pi^2)
    rw [radius_quadratic] at hime
    rw [mul_add,radius_pi] at hre
    nlinarith
  calc
    _ ≤ 4*Real.pi*Real.exp (Real.pi*z.re+1/(8*(20:ℝ)^2)+2*Real.pi^2*(20:ℝ)^2*z.im^2) := hg
    _ ≤ 4*Real.pi*Real.exp (Real.pi*x+1) := by gcongr
    _ = (4*Real.pi*Real.exp (Real.pi*x))*Real.exp 1 := by rw [Real.exp_add];ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le
        (show 0≤4*Real.pi*Real.exp (Real.pi*x) by positivity)
      convert hm using 1 <;> first | rfl | ring
lemma moment_negative_bound (T x : ℝ) (k : Nat) (hT : 20≤T) :
    ‖𝓕 (moment T k) x‖/((k.factorial:ℝ)*(512:ℝ)^k)≤
      (12*Real.pi*Real.exp (Real.pi*x))*(5/16:ℝ)^k := by
  have hc := moment_fourier_cauchy T x radius (12*Real.pi*Real.exp (Real.pi*x)) k radius_pos
    (transform_sphere_bound T x hT)
  have hb := div_le_div_of_nonneg_right hc (show 0≤(512:ℝ)^k by positivity)
  have he : (12*Real.pi*Real.exp (Real.pi*x)/radius^k)/(512:ℝ)^k=
      (12*Real.pi*Real.exp (Real.pi*x))*(40*Real.pi/512)^k := by
    unfold radius
    rw [div_pow]
    field_simp [Real.pi_ne_zero]
    rw [div_pow,one_pow]
    field_simp
  rw [←div_mul_eq_div_div,he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [Real.pi_lt_four]
end RHHighGammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory Set
namespace RHHighMomentEnvelope
lemma exp_neg_le_factorial_div_pow (v : ℝ) (hv : 0<v) (M : Nat) :
    Real.exp (-v)≤(M.factorial:ℝ)/v^M := by
  have hp := Real.pow_div_factorial_le_exp v hv.le M
  have hf : (0:ℝ)<M.factorial := by exact_mod_cast Nat.factorial_pos M
  rw [div_le_iff₀ hf] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-v)).le
  have he : Real.exp v*(M.factorial:ℝ)*Real.exp (-v)=(M.factorial:ℝ) := by
    calc
      _ = M.factorial*(Real.exp v*Real.exp (-v)) := by ring
      _ = _ := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  rw [he] at hm
  exact (le_div_iff₀ (pow_pos hv M)).mpr (by simpa [mul_comm] using hm)
lemma exp_exp_moment_envelope (u y : ℝ) (hu : 0<u) (M : Nat) :
    Real.exp (-u*Real.exp y)≤((M.factorial:ℝ)/u^M)*Real.exp (-(M:ℝ)*y) := by
  have hp := exp_neg_le_factorial_div_pow (u*Real.exp y) (mul_pos hu (Real.exp_pos _)) M
  have he : (Real.exp y)^M=Real.exp ((M:ℝ)*y) := (Real.exp_nat_mul y M).symm
  have hne : Real.exp ((M:ℝ)*y)≠0 := (Real.exp_pos _).ne'
  rw [mul_pow,he] at hp
  have hr : (M.factorial:ℝ)/(u^M*Real.exp ((M:ℝ)*y))=
      ((M.factorial:ℝ)/u^M)*Real.exp (-(M:ℝ)*y) := by
    rw [show -(M:ℝ)*y= -((M:ℝ)*y) by ring,Real.exp_neg]
    ring
  simpa only [neg_mul,hr] using hp
lemma sin_small_lower (δ : ℝ) (hδ : 0≤δ) (hδ' : δ≤1/100) :
    (999/1000:ℝ)*δ≤Real.sin δ := by
  have hs := Real.sin_ge_sub_cube hδ
  have hsq : δ^2≤1/10000 := by nlinarith
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hsq)]
end RHHighMomentEnvelope
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaRotation
open RHHighGammaFourier RHHighMomentEnvelope
noncomputable def momentMajorant (T h x α : ℝ) (M : Nat) (y : ℝ) : ℝ :=
  ((M.factorial:ℝ)/(Real.cos α)^M)*(Real.sqrt (2*Real.pi)*h)*
    Real.exp ((1/4-(M:ℝ))*y+Real.pi*T/4+
      h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2)
lemma kernel_moment_le (T h x y α : ℝ) (M : Nat) (hh : 0<h) (hcos : 0<Real.cos α) :
    ‖kernel T h x ((y:ℂ)+(α:ℂ)*I)‖ ≤ momentMajorant T h x α M y := by
  rw [kernel_norm T h x y α hh]
  unfold momentMajorant
  have he : -Real.exp y*Real.cos α+y/4+Real.pi*T/4+
      h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2=
      -(Real.cos α)*Real.exp y+(y/4+Real.pi*T/4+
        h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2) := by ring
  rw [he,Real.exp_add]
  have hm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (exp_exp_moment_envelope (Real.cos α) y hcos M)
      (Real.exp_pos (y/4+Real.pi*T/4+
        h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2)).le)
    (show 0≤Real.sqrt (2*Real.pi)*h by positivity)
  have he' : -(M:ℝ)*y+(y/4+Real.pi*T/4+
      h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2)=
      (1/4-(M:ℝ))*y+Real.pi*T/4+
        h^2/2*((Real.pi/4-α/2)^2-(y/2-2*Real.pi*x)^2)-T*α/2 := by ring
  calc
    _ ≤ _ := hm
    _ = _ := by rw [mul_assoc,mul_assoc,←Real.exp_add,he'];ring
lemma moment_majorant_quadratic (T h x α y : ℝ) (M : Nat) :
    momentMajorant T h x α M y=
      (((M.factorial:ℝ)/(Real.cos α)^M)*(Real.sqrt (2*Real.pi)*h))*
        Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+1/4-(M:ℝ))*y+
          (Real.pi*T/4+h^2/2*(Real.pi/4-α/2)^2-2*h^2*Real.pi^2*x^2-T*α/2)) := by
  unfold momentMajorant
  congr 1
  congr 1
  ring
lemma moment_majorant_integrable (T h x α : ℝ) (M : Nat) (hh : 0<h) :
    Integrable (momentMajorant T h x α M) := by
  have he : momentMajorant T h x α M=(fun y : ℝ =>
      (((M.factorial:ℝ)/(Real.cos α)^M)*(Real.sqrt (2*Real.pi)*h))*
        Real.exp ((-h^2/8)*y^2+(h^2*Real.pi*x+1/4-(M:ℝ))*y+
          (Real.pi*T/4+h^2/2*(Real.pi/4-α/2)^2-2*h^2*Real.pi^2*x^2-T*α/2))) := by
    ext y
    exact moment_majorant_quadratic T h x α y M
  rw [he]
  exact (real_quadratic_integrable _ _ _ (by nlinarith [sq_pos_of_pos hh])).const_mul _
lemma moment_majorant_integral (T h x α : ℝ) (M : Nat) (hh : 0<h) :
    (∫ y : ℝ, momentMajorant T h x α M y)=
      (4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*Real.exp (
        Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+
          2*(1/4-(M:ℝ))^2/h^2+4*Real.pi*x*(1/4-(M:ℝ))) := by
  simp_rw [moment_majorant_quadratic]
  rw [integral_const_mul,integral_real_quadratic _ _ _ (by nlinarith [sq_pos_of_pos hh])]
  rw [show -(-h^2/8)=h^2/8 by ring]
  have hp : ((M.factorial:ℝ)/(Real.cos α)^M)*(Real.sqrt (2*Real.pi)*h)*
      Real.sqrt (Real.pi/(h^2/8))=4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M := by
    rw [mul_assoc,gaussian_prefactor h hh]
    ring
  rw [←mul_assoc,hp]
  congr 2
  field_simp [hh.ne']
  ring
lemma gamma_fourier_moment_bound (T h x α : ℝ) (M : Nat) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α<Real.pi/2) :
    ‖𝓕 (gammaWindow T h) x‖ ≤
      (4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*Real.exp (
        Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+
          2*(1/4-(M:ℝ))^2/h^2+4*Real.pi*x*(1/4-(M:ℝ))) := by
  rw [gamma_contour_rotation T h x α hT hh hα hα'.le]
  have hc : 0<Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hα'⟩
  calc
    _ ≤ ∫ y : ℝ, ‖kernel T h x ((y:ℂ)+(α:ℂ)*I)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, momentMajorant T h x α M y :=
      integral_mono (kernel_line_integrable T h x α hT hh hα hα'.le).norm
        (moment_majorant_integrable T h x α M hh) (fun y => kernel_moment_le T h x y α M hh hc)
    _ = _ := moment_majorant_integral T h x α M hh
end RHHighGammaRotation
end
section
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
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
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
  have he : Real.exp '' (Set.univ:Set ℝ)=Set.Ioi 0 := by simpa using Real.range_exp
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
end
section
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
    (∫ y : ℝ in Set.Ioi 0, Complex.exp (-(s/2)*(y:ℂ)))=2/s := by
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
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
  have hy : IntegrableOn (fun y : ℝ => Real.exp (-y/4)) (Set.Ioi 0) := by
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
      (1/2:ℂ)*∫ y : ℝ in Set.Ioi 0, Complex.exp ((-y/4:ℝ):ℂ)*Q T h x (-ε*y) := by
  have hi (t : ℝ) : (1/2:ℂ)*(∫ y : ℝ in Set.Ioi 0, poleJoint ε T h x t y)=
      poleWindow ε T h t*Complex.exp (((-2*Real.pi*t*x:ℝ):ℂ)*I) := by
    simp only [poleJoint,integral_mul_const]
    rw [laplace_half _ (by rw [sline_re];norm_num)]
    unfold poleWindow
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = (1/2:ℂ)*∫ t : ℝ, ∫ y : ℝ in Set.Ioi 0, poleJoint ε T h x t y := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hi]
      simp only [smul_eq_mul,mul_comm]
    _ = (1/2:ℂ)*∫ y : ℝ in Set.Ioi 0, ∫ t : ℝ, poleJoint ε T h x t y := by
      rw [integral_integral_swap (pole_joint_integrable ε T h x hh)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      exact pole_joint_inner ε T h x y hh
end RHHighPoleFourier
end
section
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
end
section
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
end
section
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
    𝓕 (poleWindow (-1) T h) x=(∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)/2 := by
  rw [pole_window_fourier (-1) T h x hh]
  simp only [neg_neg,one_mul]
  change (1/2:ℂ)*(∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)=_
  ring
lemma full_fourier_series (T h x : ℝ) (hh : 0<h) :
    𝓕 (fullWindow T h) x=(∑' n : Nat, dirichletTerm T h x n)-
      2*(Real.pi:ℂ)*Complex.exp (
        ((1/(8*h^2)-T^2/(2*h^2)-Real.pi*x:ℝ):ℂ)+
        I*((2*Real.pi*T*x-T/(2*h^2)-Real.pi/8:ℝ):ℂ)) := by
  rw [full_fourier_decomposition T h x hh,entire_fourier_correction T h x hh,
    pole_plus_fourier T h x hh,pole_minus_fourier T h x hh]
  have hi : (∫ y : ℝ in Iio 0, negativeKernel T h x y)+
      (∫ y : ℝ in Set.Ioi 0, negativeKernel T h x y)=∫ y : ℝ, negativeKernel T h x y := by
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
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory Set
namespace RHHighDirichletTail
lemma power_tail (p : ℝ) (hp : 1<p) (J : Nat) (hJ : 0<J) :
    (∑' n : Nat, ((n+J+1:Nat):ℝ)^(-p))≤(J:ℝ)^(1-p)/(p-1) := by
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  have ha : AntitoneOn (fun t : ℝ => t^(-p)) (Ici (J:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hJr.trans_le hx) hxy (by linarith)
  have ht := ha.tsum_comp_add_le_integral J
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hJr)
    (fun t ht => Real.rpow_nonneg (hJr.trans ht).le _)
  apply ht.trans_eq
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) hJr,
    show -p+1=1-p by ring]
  rw [show 1-p= -(p-1) by ring,neg_div_neg_eq]
end RHHighDirichletTail
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighFiniteDirichlet
open RHHighGammaFourier RHHighGammaRotation RHHighPlattFourier RHHighDirichletTail
noncomputable def boundConstant (T h α : ℝ) (M : Nat) : ℝ :=
  (4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*Real.exp (
    Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/h^2)
lemma weight_norm (T a : ℝ) : ‖dirichletWeight T a‖=Real.exp (-Real.log a/2) := by
  rw [dirichletWeight,Complex.norm_exp]
  congr 1
  simp only [neg_re,mul_re,add_re,div_re,ofReal_re,ofReal_im,I_re,I_im,mul_im]
  norm_num
  ring
lemma shifted_gamma_bound (T h x α a : ℝ) (M : Nat) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α<Real.pi/2) (ha : 0<a) :
    ‖dirichletWeight T a*𝓕 (gammaWindow T h) (x+Real.log a/(2*Real.pi))‖ ≤
      boundConstant T h α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ)))*a^(-(2*(M:ℝ))) := by
  rw [norm_mul,weight_norm]
  have hg := gamma_fourier_moment_bound T h (x+Real.log a/(2*Real.pi)) α M hT hh hα hα'
  apply (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le).trans_eq
  unfold boundConstant
  rw [Real.rpow_def_of_pos ha]
  have he : -Real.log a/2+(Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+
      2*(1/4-(M:ℝ))^2/h^2+4*Real.pi*(x+Real.log a/(2*Real.pi))*(1/4-(M:ℝ)))=
      (Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/h^2)+
        4*Real.pi*x*(1/4-(M:ℝ))+Real.log a*(-(2*(M:ℝ))) := by
    field_simp [Real.pi_ne_zero]
    ring
  calc
    _ = (4*Real.pi*(M.factorial:ℝ)/(Real.cos α)^M)*
      (Real.exp (-Real.log a/2)*Real.exp (Real.pi*T/4-T*α/2+h^2/2*(Real.pi/4-α/2)^2+
        2*(1/4-(M:ℝ))^2/h^2+4*Real.pi*(x+Real.log a/(2*Real.pi))*(1/4-(M:ℝ)))) := by ring
    _ = _ := by rw [←Real.exp_add,he,Real.exp_add,Real.exp_add];ring
lemma dirichlet_term_bound (T h x α : ℝ) (M : Nat) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α<Real.pi/2) (n : Nat) :
    ‖dirichletTerm T h x n‖ ≤
      (boundConstant T h α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ)))*Real.pi^(-(M:ℝ)))*
        (n+1:ℝ)^(-(2*(M:ℝ))) := by
  have ht := shifted_gamma_bound T h x α ((n+1:ℝ)*Real.sqrt Real.pi) M hT hh hα hα' (by positivity)
  apply ht.trans_eq
  rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,
    ←Real.rpow_mul Real.pi_pos.le]
  rw [show (1/2:ℝ)*(-(2*(M:ℝ)))= -(M:ℝ) by ring]
  ring
lemma dirichlet_norm_summable (T h x : ℝ) (hh : 0<h) :
    Summable (fun n : Nat => ‖dirichletTerm T h x n‖) := by
  apply (RHHighThetaGamma.kernel_integral_norm_summable T h x hh).of_nonneg_of_le
    (fun n => norm_nonneg _)
  intro n
  rw [dirichlet_term_eq T h x hh]
  exact norm_integral_le_integral_norm _
end RHHighFiniteDirichlet
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaComplexFourier
open RHHighGammaFourier RHHighGammaRotation RHHighFiniteDirichlet
lemma transform_complex_moment_bound (T u v α : ℝ) (M : Nat)
    (hT : 0≤T+2*Real.pi*(20:ℝ)^2*v) (hα : 0≤α) (hα' : α<Real.pi/2) :
    ‖transform T 20 ((u:ℂ)+(v:ℂ)*I)‖ ≤
      boundConstant (T+2*Real.pi*(20:ℝ)^2*v) 20 α M*
        Real.exp (4*Real.pi*u*(1/4-(M:ℝ))+2*Real.pi^2*(20:ℝ)^2*v^2) := by
  rw [transform_complex_shift T 20 u v (by norm_num),norm_mul,Complex.norm_exp]
  have he : ((((2*Real.pi^2*(20:ℝ)^2*v^2:ℝ):ℂ)-I*((4*Real.pi^2*(20:ℝ)^2*u*v:ℝ):ℂ))).re=
      2*Real.pi^2*(20:ℝ)^2*v^2 := by
    simp only [sub_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero]
  rw [he]
  have hg := gamma_fourier_moment_bound (T+2*Real.pi*(20:ℝ)^2*v) 20 u α M hT
    (by norm_num) hα hα'
  apply (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le).trans_eq
  unfold boundConstant
  simp only [Real.exp_add]
  ring
end RHHighGammaComplexFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHHighGammaCircle
open RHHighGammaFourier RHHighGammaComplexFourier RHHighFiniteDirichlet RHHighGammaTaylorFourier
lemma sphere_geometry (T x : ℝ) (hT : 20≤T) (z : ℂ) (hz : z∈sphere (x:ℂ) radius) :
    0≤T+2*Real.pi*(20:ℝ)^2*z.im ∧ x-radius≤z.re ∧
      2*Real.pi*(20:ℝ)^2*z.im≤20 ∧ 2*Real.pi^2*(20:ℝ)^2*z.im^2≤1/2 := by
  have hn : ‖z-(x:ℂ)‖=radius := mem_sphere_iff_norm.mp hz
  have hi : |z.im|≤radius := by simpa only [sub_im,ofReal_im,sub_zero,hn] using Complex.abs_im_le_norm (z-(x:ℂ))
  have hr : |z.re-x|≤radius := by simpa only [sub_re,ofReal_re,hn] using Complex.abs_re_le_norm (z-(x:ℂ))
  have hl := mul_le_mul_of_nonneg_left (abs_le.mp hi).1 (by positivity : 0≤800*Real.pi)
  have hu := mul_le_mul_of_nonneg_left (abs_le.mp hi).2 (by positivity : 0≤800*Real.pi)
  have hp : 800*Real.pi*radius=20 := by rw [mul_assoc,radius_pi];norm_num
  have hs : z.im^2≤radius^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z.im) radius_pos.le).mpr hi
  have hv := mul_le_mul_of_nonneg_left hs (by positivity : 0≤800*Real.pi^2)
  rw [radius_quadratic] at hv
  constructor
  · nlinarith
  constructor
  · have := (abs_le.mp hr).1
    linarith
  constructor
  · nlinarith
  · nlinarith
lemma shifted_constant (T α v : ℝ) (M : Nat) :
    boundConstant (T+2*Real.pi*(20:ℝ)^2*v) 20 α M=
      boundConstant T 20 α M*Real.exp ((Real.pi/4-α/2)*(2*Real.pi*(20:ℝ)^2*v)) := by
  unfold boundConstant
  have he : Real.pi*(T+2*Real.pi*(20:ℝ)^2*v)/4-(T+2*Real.pi*(20:ℝ)^2*v)*α/2+
      (20:ℝ)^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/(20:ℝ)^2=
      (Real.pi*T/4-T*α/2+(20:ℝ)^2/2*(Real.pi/4-α/2)^2+2*(1/4-(M:ℝ))^2/(20:ℝ)^2)+
        (Real.pi/4-α/2)*(2*Real.pi*(20:ℝ)^2*v) := by ring
  rw [he,Real.exp_add,mul_assoc]
  ring
end RHHighGammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHHighGammaCircle
open RHHighGammaFourier RHHighGammaComplexFourier RHHighFiniteDirichlet RHHighGammaTaylorFourier
lemma transform_positive_sphere_bound (T x α : ℝ) (M : Nat) (hT : 20≤T)
    (hα : 0≤α) (hα' : α<Real.pi/2) (hM : 0<M) :
    ∀ z ∈ sphere (x:ℂ) radius, ‖transform T 20 z‖ ≤
      boundConstant T 20 α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ))+
        5*Real.pi+1/2+((M:ℝ)-1/4)/10) := by
  intro z hz
  have geom := sphere_geometry T x hT z hz
  have hg := transform_complex_moment_bound T z.re z.im α M geom.1 hα hα'
  rw [Complex.re_add_im,shifted_constant] at hg
  have hc0 : 0≤Real.pi/4-α/2 := by linarith
  have hc1 : Real.pi/4-α/2≤Real.pi/4 := by linarith
  have hm : (Real.pi/4-α/2)*(2*Real.pi*(20:ℝ)^2*z.im)≤5*Real.pi := by
    have he := mul_le_mul_of_nonneg_left geom.2.2.1 hc0
    nlinarith
  have hMr : (1:ℝ)≤M := by exact_mod_cast hM
  have hβ : 4*Real.pi*(1/4-(M:ℝ))≤0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hr := mul_le_mul_of_nonpos_left geom.2.1 hβ
  have he : (4*Real.pi*(1/4-(M:ℝ)))*radius= -((M:ℝ)-1/4)/10 := by
    unfold radius
    field_simp [Real.pi_ne_zero]
    ring
  have hu : 4*Real.pi*z.re*(1/4-(M:ℝ))≤4*Real.pi*x*(1/4-(M:ℝ))+((M:ℝ)-1/4)/10 := by
    nlinarith
  have hB : 0≤boundConstant T 20 α M := by
    have hc : 0<Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hα'⟩
    unfold boundConstant
    positivity
  calc
    _ ≤ _ := hg
    _ = boundConstant T 20 α M*Real.exp ((Real.pi/4-α/2)*(2*Real.pi*(20:ℝ)^2*z.im)+
      4*Real.pi*z.re*(1/4-(M:ℝ))+2*Real.pi^2*(20:ℝ)^2*z.im^2) := by
      rw [mul_assoc,←Real.exp_add];congr 2;ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Real.exp_le_exp.mpr
      nlinarith [geom.2.2.2]
end RHHighGammaCircle
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighGammaTimeTail
open RHHighGammaFourier RHHighGammaTaylorFourier
noncomputable def scaledMoment (T : ℝ) (k : Nat) (t : ℝ) : ℂ :=
  moment T k t/((k.factorial:ℂ)*(512:ℂ)^k)
lemma scaled_moment_norm (T t : ℝ) (k : Nat) :
    ‖scaledMoment T k t‖≤6*Real.exp (|t|/64-t^2/800) := by
  have hd : (0:ℝ)<(k.factorial:ℝ)*(512:ℝ)^k := by positivity
  have hg := TaoFivePrimes.rh_high_height_scaled_gamma_bound.2 T t 20 k
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num] at hg
  have hbase : ‖moment T k t‖≤6*(2*Real.pi*|t|)^k*Real.exp (-t^2/800) := by
    simpa only [moment,gammaWindow,window,Complex.ofReal_exp,
      show (2*(20:ℝ)^2)=800 by norm_num] using hg
  rw [scaledMoment,norm_div,norm_mul,norm_natCast,norm_pow,norm_ofNat]
  apply (div_le_div_of_nonneg_right hbase hd.le).trans
  have he : (6*(2*Real.pi*|t|)^k*Real.exp (-t^2/800))/((k.factorial:ℝ)*512^k)=
      6*((Real.pi*|t|/256)^k/(k.factorial:ℝ))*Real.exp (-t^2/800) := by
    rw [div_pow]
    field_simp
    rw [show (512:ℝ)^k=(2:ℝ)^k*256^k by rw [←mul_pow];norm_num]
    ring
  rw [he]
  have hp := Real.pow_div_factorial_le_exp (Real.pi*|t|/256) (by positivity) k
  have hu : Real.pi*|t|/256≤|t|/64 := by nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr Real.pi_lt_four.le)]
  calc
    _ ≤ 6*Real.exp (Real.pi*|t|/256)*Real.exp (-t^2/800) := by gcongr
    _ ≤ 6*Real.exp (|t|/64)*Real.exp (-t^2/800) := by gcongr
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring
lemma scaled_moment_tail (T t : ℝ) (k : Nat) (ht : 256≤|t|) :
    ‖scaledMoment T k t‖≤6*Real.exp (-|t|/4) := by
  apply (scaled_moment_norm T t k).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_abs t,mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht)]
lemma positive_alias_term (T t : ℝ) (k n : Nat) (ht : -256≤t) :
    ‖scaledMoment T k (t+(n+1:ℝ)*512)‖≤6*Real.exp (-64*(n+1:ℝ)) := by
  have hn : (0:ℝ)≤n := by positivity
  have ha : 256≤t+(n+1:ℝ)*512 := by linarith
  have habs : |t+(n+1:ℝ)*512|=t+(n+1:ℝ)*512 := abs_of_nonneg (by linarith)
  apply (scaled_moment_tail T _ k (by rw [habs];exact ha)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [habs]
  linarith
lemma negative_alias_term (T t : ℝ) (k n : Nat) (ht : t≤256) :
    ‖scaledMoment T k (t-(n+1:ℝ)*512)‖≤6*Real.exp (-64*(n+1:ℝ)) := by
  have hn : (0:ℝ)≤n := by positivity
  have ha : t-(n+1:ℝ)*512≤ -256 := by linarith
  have habs : |t-(n+1:ℝ)*512|= -(t-(n+1:ℝ)*512) := abs_of_nonpos (by linarith)
  apply (scaled_moment_tail T _ k (by rw [habs];linarith)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [habs]
  linarith
end RHHighGammaTimeTail
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set Metric
open scoped FourierTransform Topology
namespace RHHighScaledMomentFourier
open RHHighGammaCircle RHHighGammaComplexFourier RHHighGammaTaylorFourier RHHighGammaTimeTail RHHighFiniteDirichlet
lemma fourier_scaled (T x : ℝ) (k : Nat) :
    𝓕 (scaledMoment T k) x=𝓕 (moment T k) x/((k.factorial:ℂ)*(512:ℂ)^k) := by
  simp only [Real.fourier_real_eq_integral_exp_smul,scaledMoment,smul_eq_mul,div_eq_mul_inv,mul_assoc]
  simp only [←mul_assoc]
  rw [integral_mul_const]
lemma norm_fourier_scaled (T x : ℝ) (k : Nat) :
    ‖𝓕 (scaledMoment T k) x‖=‖𝓕 (moment T k) x‖/((k.factorial:ℝ)*(512:ℝ)^k) := by
  rw [fourier_scaled,norm_div,norm_mul,norm_natCast,norm_pow,norm_ofNat]
lemma scaled_cauchy_bound (T x C : ℝ) (k : Nat) (hC : 0≤C)
    (hB : ∀ z ∈ sphere (x:ℂ) radius, ‖transform T 20 z‖≤C) :
    ‖𝓕 (scaledMoment T k) x‖≤C*(5/16:ℝ)^k := by
  rw [norm_fourier_scaled]
  have hc := moment_fourier_cauchy T x radius C k radius_pos hB
  have hb := div_le_div_of_nonneg_right hc (show 0≤(512:ℝ)^k by positivity)
  have he : (C/radius^k)/(512:ℝ)^k=C*(40*Real.pi/512)^k := by
    unfold radius
    rw [div_pow]
    field_simp [Real.pi_ne_zero]
    rw [div_pow,one_pow]
    field_simp
  rw [←div_mul_eq_div_div,he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [Real.pi_lt_four]
lemma scaled_negative_bound (T x : ℝ) (k : Nat) (hT : 20≤T) :
    ‖𝓕 (scaledMoment T k) x‖≤12*Real.pi*Real.exp (Real.pi*x)*(5/16:ℝ)^k := by
  rw [norm_fourier_scaled]
  exact moment_negative_bound T x k hT
lemma scaled_positive_bound (T x α : ℝ) (M k : Nat) (hT : 20≤T)
    (hα : 0≤α) (hα' : α<Real.pi/2) (hM : 0<M) :
    ‖𝓕 (scaledMoment T k) x‖≤
      (boundConstant T 20 α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ))+
        5*Real.pi+1/2+((M:ℝ)-1/4)/10))*(5/16:ℝ)^k := by
  apply scaled_cauchy_bound
  · have hc : 0<Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hα'⟩
    unfold boundConstant
    positivity
  · exact transform_positive_sphere_bound T x α M hT hα hα' hM
end RHHighScaledMomentFourier
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform
namespace RHHighGammaFixedBounds
open RHHighGammaTimeTail RHHighScaledMomentFourier RHHighFiniteDirichlet
noncomputable def angle (T : ℝ) : ℝ := Real.pi/2-1/T
lemma angle_admissible (T : ℝ) (hT : 3000000000≤T) :
    0≤angle T ∧ angle T<Real.pi/2 := by
  have ht : 0<T := by linarith
  have hi : 1/T≤1 := (div_le_one ht).mpr (by linarith)
  unfold angle
  constructor <;> linarith [Real.pi_gt_three,div_pos (by norm_num : (0:ℝ)<1) ht]
lemma fixed_constant (T : ℝ) (hT : 3000000000≤T ∧ T≤4000000000) :
    boundConstant T 20 (angle T) 122≤Real.exp 10000 := by
  have ht : 0<T := by linarith
  have hlo : (1:ℝ)/4000000000≤1/T := div_le_div_of_nonneg_left (by norm_num) ht hT.2
  have hhi : (1:ℝ)/T≤1/100 := (div_le_div_iff₀ ht (by norm_num)).mpr (by linarith)
  have hc : (1:ℝ)/2^33≤Real.cos (angle T) := by
    rw [angle,Real.cos_pi_div_two_sub]
    have hs := RHHighMomentEnvelope.sin_small_lower (1/T) (by positivity) hhi
    linarith
  have hcp : 0<Real.cos (angle T) := lt_of_lt_of_le (by positivity) hc
  have hf : 4*Real.pi*((122).factorial:ℝ)/(Real.cos (angle T))^122≤(2:ℝ)^5000 := by
    calc
      _ ≤ 16*((122).factorial:ℝ)/((1:ℝ)/2^33)^122 := by
        apply div_le_div₀
        · positivity
        · nlinarith [Real.pi_lt_four]
        · positivity
        · exact pow_le_pow_left₀ (by positivity) hc _
      _ = ((16*(122).factorial*2^(33*122):Nat):ℝ) := by
        push_cast
        rw [div_pow,one_pow,one_div,div_inv_eq_mul,←pow_mul]
      _ ≤ _ := by
        exact_mod_cast (show 16*(122).factorial*2^(33*122)≤2^5000 from by decide +kernel)
  have heq : Real.pi*T/4-T*angle T/2+(20:ℝ)^2/2*(Real.pi/4-angle T/2)^2+
      2*(1/4-(122:ℝ))^2/(20:ℝ)^2=1/2+50/T^2+237169/3200 := by
    unfold angle
    field_simp
    ring
  have hs : 50/T^2≤1/2 := (div_le_div_iff₀ (sq_pos_of_pos ht) (by norm_num)).mpr (by nlinarith)
  have he : Real.pi*T/4-T*angle T/2+(20:ℝ)^2/2*(Real.pi/4-angle T/2)^2+
      2*(1/4-(122:ℝ))^2/(20:ℝ)^2≤80 := by rw [heq];linarith
  have hp : (2:ℝ)^5000≤Real.exp 5000 := by
    rw [show Real.exp (5000:ℝ)=(Real.exp 1)^5000 by simpa using Real.exp_nat_mul (1:ℝ) (5000:Nat)]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
  unfold boundConstant
  calc
    _ ≤ (2:ℝ)^5000*Real.exp 80 := mul_le_mul hf (Real.exp_le_exp.mpr he) (by positivity) (by positivity)
    _ ≤ Real.exp 5000*Real.exp 80 := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = Real.exp 5080 := by rw [←Real.exp_add];norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
lemma positive_frequency_alias_term (T x : ℝ) (k n : Nat)
    (hT : 3000000000≤T ∧ T≤4000000000) (hx : 0≤x) :
    ‖𝓕 (scaledMoment T k) (x+32*(n+1:ℝ))‖≤Real.exp (-128*(n+1:ℝ)) := by
  have ha := angle_admissible T hT.1
  have hb := scaled_positive_bound T (x+32*(n+1:ℝ)) (angle T) 122 k
    (by linarith) ha.1 ha.2 (by norm_num)
  have hk : (5/16:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have he : 10000+(4*Real.pi*(x+32*(n+1:ℝ))*(1/4-(122:ℝ))+
      5*Real.pi+1/2+((122:ℝ)-1/4)/10)≤-128*(n+1:ℝ) := by
    have hxp : (0:ℝ)≤Real.pi*x := mul_nonneg Real.pi_pos.le hx
    have hnp : 3*(n+1:ℝ)≤Real.pi*(n+1:ℝ) := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by positivity)
    nlinarith [Real.pi_lt_four]
  calc
    _ ≤ (boundConstant T 20 (angle T) 122*Real.exp (4*Real.pi*(x+32*(n+1:ℝ))*(1/4-(122:ℝ))+
        5*Real.pi+1/2+((122:ℝ)-1/4)/10))*(5/16:ℝ)^k := hb
    _ ≤ Real.exp 10000*Real.exp (4*Real.pi*(x+32*(n+1:ℝ))*(1/4-(122:ℝ))+
        5*Real.pi+1/2+((122:ℝ)-1/4)/10) := by
      apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (fixed_constant T hT) (by positivity)) (by positivity)).trans
      exact mul_le_of_le_one_right (by positivity) hk
    _ = Real.exp (10000+(4*Real.pi*(x+32*(n+1:ℝ))*(1/4-(122:ℝ))+
        5*Real.pi+1/2+((122:ℝ)-1/4)/10)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr he
lemma negative_frequency_alias_term (T x : ℝ) (k n : Nat) (hT : 20≤T) (hx : x≤5) :
    ‖𝓕 (scaledMoment T k) (x-32*(n+1:ℝ))‖≤48*Real.exp (-81*(n+1:ℝ)) := by
  have hb := scaled_negative_bound T (x-32*(n+1:ℝ)) k hT
  have hk : (5/16:ℝ)^k≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hs : x-32*(n+1:ℝ)≤0 := by linarith
  have he : Real.pi*(x-32*(n+1:ℝ))≤-81*(n+1:ℝ) := by
    have hp := mul_le_mul_of_nonpos_right Real.pi_gt_three.le hs
    nlinarith
  calc
    _ ≤ 12*Real.pi*Real.exp (Real.pi*(x-32*(n+1:ℝ)))*(5/16:ℝ)^k := hb
    _ ≤ 12*Real.pi*Real.exp (Real.pi*(x-32*(n+1:ℝ))) := mul_le_of_le_one_right (by positivity) hk
    _ ≤ _ := mul_le_mul (by linarith [Real.pi_lt_four]) (Real.exp_le_exp.mpr he) (by positivity) (by norm_num)
end RHHighGammaFixedBounds
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex
namespace RHHighGammaBandwidthTwo
open RHHighFiniteDirichlet
noncomputable def angle (T : ℝ) : ℝ := Real.pi/2-400/T
lemma angle_admissible (T : ℝ) (hT : 3000000000≤T) :
    0≤angle T ∧ angle T<Real.pi/2 := by
  have ht : 0 < T := by linarith
  have he : 400/T≤1 := (div_le_one ht).mpr (by linarith)
  unfold angle
  constructor <;> linarith [Real.pi_gt_three,div_pos (by norm_num : (0:ℝ)<400) ht]
lemma cosine_lower (T : ℝ) (hT : 3000000000≤T) : 200/T≤Real.cos (angle T) := by
  have ht : 0 < T := by linarith
  have he : 400/T≤1/100 := (div_le_div_iff₀ ht (by norm_num)).mpr (by linarith)
  have h := RHHighMomentEnvelope.sin_small_lower (400/T) (by positivity) he
  rw [angle,Real.cos_pi_div_two_sub]
  calc
    _ ≤ ((999/1000:ℝ)*400)/T := div_le_div_of_nonneg_right (by norm_num) ht.le
    _ = (999/1000:ℝ)*(400/T) := by ring
    _ ≤ _ := h
lemma T_exp_bound (T : ℝ) (hT : T≤4000000000) : T≤Real.exp (45/2) := by
  have hp : (27/10:ℝ)^45≤Real.exp 45 := by
    rw [show Real.exp (45:ℝ)=(Real.exp 1)^45 by simpa using Real.exp_nat_mul (1:ℝ) (45:Nat)]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have hs : Real.exp (45/2)^2=Real.exp (45:ℝ) := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
  have hh : (4000000000:ℝ)^2≤(27/10:ℝ)^45 := by norm_num
  nlinarith [Real.exp_pos (45/2)]
lemma fixed_constant (T : ℝ) (hT : 3000000000≤T ∧ T≤4000000000) :
    boundConstant T 20 (angle T) 200≤Real.exp 4920 := by
  have ht : 0 < T := by linarith
  have hc := cosine_lower T hT.1
  have hc0 : 0 < Real.cos (angle T) := lt_of_lt_of_le (by positivity) hc
  have hf : (200:Nat).factorial≤200^200 := Nat.factorial_le_pow 200
  have hpref : 4*Real.pi*((200).factorial:ℝ)/(Real.cos (angle T))^200≤16*T^200 := by
    calc
      _ ≤ 16*(200:ℝ)^200/(200/T)^200 := by
        apply div_le_div₀
        · positivity
        · have hfr : ((200).factorial:ℝ)≤(200:ℝ)^200 := by exact_mod_cast hf
          nlinarith [Real.pi_lt_four]
        · positivity
        · exact pow_le_pow_left₀ (by positivity) hc _
      _ = _ := by rw [div_pow];field_simp
  have heq : Real.pi*T/4-T*angle T/2+(20:ℝ)^2/2*(Real.pi/4-angle T/2)^2+
      2*(1/4-(200:ℝ))^2/(20:ℝ)^2=200+8000000/T^2+638401/3200 := by
    unfold angle
    field_simp
    ring
  have hs : 8000000/T^2≤1 := (div_le_one (sq_pos_of_pos ht)).mpr (by nlinarith [hT.1])
  have he : Real.pi*T/4-T*angle T/2+(20:ℝ)^2/2*(Real.pi/4-angle T/2)^2+
      2*(1/4-(200:ℝ))^2/(20:ℝ)^2≤401 := by rw [heq];linarith
  have h16 : (16:ℝ)≤Real.exp 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/3) (by linarith [Real.exp_one_gt_d9] : (8/3:ℝ)≤Real.exp 1) 3
    rw [←Real.exp_nat_mul] at h
    norm_num at h ⊢
    linarith
  have hpow : T^200≤Real.exp 4500 := by
    have h := pow_le_pow_left₀ ht.le (T_exp_bound T hT.2) 200
    rw [←Real.exp_nat_mul] at h
    norm_num at h
    exact h
  unfold boundConstant
  calc
    _ ≤ (16*T^200)*Real.exp 401 := mul_le_mul hpref (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
    _ ≤ (Real.exp 3*Real.exp 4500)*Real.exp 401 :=
      mul_le_mul_of_nonneg_right (mul_le_mul h16 hpow (by positivity) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp 4904 := by rw [←Real.exp_add,←Real.exp_add];norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
end RHHighGammaBandwidthTwo
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 20000
open Complex
namespace RHHighGammaBandwidthTwo
lemma cosine_tight (T : ℝ) (hT : 3000000000≤T) : 399/T≤Real.cos (angle T) := by
  have ht : 0 < T := by linarith
  have he : 400/T≤1/100 := (div_le_div_iff₀ ht (by norm_num)).mpr (by linarith)
  have h := RHHighMomentEnvelope.sin_small_lower (400/T) (by positivity) he
  rw [angle,Real.cos_pi_div_two_sub]
  calc
    _ ≤ ((999/1000:ℝ)*400)/T := div_le_div_of_nonneg_right (by norm_num) ht.le
    _ = (999/1000:ℝ)*(400/T) := by ring
    _ ≤ _ := h
lemma T_exp22 (T : ℝ) (hT : T≤3300000000) : T≤Real.exp 22 := by
  have hp : (2718/1000:ℝ)^22≤Real.exp 22 := by
    rw [show Real.exp (22:ℝ)=(Real.exp 1)^22 by simpa using Real.exp_nat_mul (1:ℝ) (22:Nat)]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have hh : (3300000000:ℝ)≤(2718/1000:ℝ)^22 := by norm_num
  linarith
lemma factorial_ratio : (76/399:ℝ)^200≤Real.exp (-327) := by
  have h : Real.exp 327≤(399/76:ℝ)^200 := by
    calc
      _ = (Real.exp 1)^327 := by simpa using (Real.exp_nat_mul (1:ℝ) (327:Nat))
      _ ≤ (11/4:ℝ)^327 := pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
      _ ≤ _ := by norm_num
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) h
  rw [one_div,←inv_pow,inv_div] at hi
  simpa only [Real.exp_neg,one_div] using hi
lemma fixed_constant_tight (T : ℝ) (hT : 3000000000≤T ∧ T≤3300000000) :
    RHHighFiniteDirichlet.boundConstant T 20 (angle T) 200≤Real.exp 4477 := by
  have ht : 0 < T := by linarith
  have hc := cosine_tight T hT.1
  have hf : (200:Nat).factorial≤76^200 := by decide +kernel
  have hpref : 4*Real.pi*((200).factorial:ℝ)/(Real.cos (angle T))^200≤
      16*(76/399:ℝ)^200*T^200 := by
    calc
      _ ≤ 16*(76:ℝ)^200/(399/T)^200 := by
        apply div_le_div₀
        · positivity
        · have hfr : ((200).factorial:ℝ)≤(76:ℝ)^200 := by exact_mod_cast hf
          nlinarith [Real.pi_lt_four]
        · positivity
        · exact pow_le_pow_left₀ (by positivity) hc _
      _ = _ := by rw [div_pow,div_pow];field_simp
  have heq : Real.pi*T/4-T*angle T/2+(20:ℝ)^2/2*(Real.pi/4-angle T/2)^2+
      2*(1/4-(200:ℝ))^2/(20:ℝ)^2=200+8000000/T^2+638401/3200 := by
    unfold angle
    field_simp
    ring
  have hs : 8000000/T^2≤1 := (div_le_one (sq_pos_of_pos ht)).mpr (by nlinarith [hT.1])
  have he : Real.pi*T/4-T*angle T/2+(20:ℝ)^2/2*(Real.pi/4-angle T/2)^2+
      2*(1/4-(200:ℝ))^2/(20:ℝ)^2≤401 := by rw [heq];linarith
  have h16 : (16:ℝ)≤Real.exp 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/3) (by linarith [Real.exp_one_gt_d9] : (8/3:ℝ)≤Real.exp 1) 3
    rw [←Real.exp_nat_mul] at h
    norm_num at h ⊢
    linarith
  have hpow : T^200≤Real.exp 4400 := by
    have h := pow_le_pow_left₀ ht.le (T_exp22 T hT.2) 200
    rw [←Real.exp_nat_mul] at h
    norm_num at h
    exact h
  unfold RHHighFiniteDirichlet.boundConstant
  calc
    _ ≤ (16*(76/399:ℝ)^200*T^200)*Real.exp 401 :=
      mul_le_mul hpref (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
    _ ≤ (Real.exp 3*Real.exp (-327)*Real.exp 4400)*Real.exp 401 := by
      gcongr
      exact factorial_ratio
    _ = Real.exp 4477 := by rw [←Real.exp_add,←Real.exp_add,←Real.exp_add];norm_num
end RHHighGammaBandwidthTwo
end
section
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped FourierTransform Topology
namespace RHHighFiniteDirichlet
open RHHighGammaFourier RHHighGammaRotation RHHighPlattFourier RHHighDirichletTail
noncomputable def tailConstant (T h x α : ℝ) (M : Nat) : ℝ :=
  boundConstant T h α M*Real.exp (4*Real.pi*x*(1/4-(M:ℝ)))*Real.pi^(-(M:ℝ))
lemma tail_constant_nonneg (T h x α : ℝ) (M : Nat) (hcos : 0<Real.cos α) :
    0≤tailConstant T h x α M := by unfold tailConstant boundConstant;positivity
lemma omitted_series_bound (T h x α : ℝ) (M J : Nat) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α<Real.pi/2) (hM : 0<M) (hJ : 0<J) :
    ‖∑' n : Nat, dirichletTerm T h x (n+J)‖ ≤
      tailConstant T h x α M*(J:ℝ)^(1-2*(M:ℝ))/(2*(M:ℝ)-1) := by
  have hMr : (1:ℝ)≤M := by exact_mod_cast hM
  have hp : 1<2*(M:ℝ) := by linarith
  have hc : 0≤tailConstant T h x α M := tail_constant_nonneg T h x α M
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hα'⟩)
  have hn : Summable (fun n : Nat => ‖dirichletTerm T h x (n+J)‖) :=
    (summable_nat_add_iff J).mpr (dirichlet_norm_summable T h x hh)
  have hp0 : Summable (fun n : Nat => (n:ℝ)^(-(2*(M:ℝ)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hps : Summable (fun n : Nat => ((n+J+1:Nat):ℝ)^(-(2*(M:ℝ)))) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (J+1)).mpr hp0
  have hb (n : Nat) : ‖dirichletTerm T h x (n+J)‖≤
      tailConstant T h x α M*((n+J+1:Nat):ℝ)^(-(2*(M:ℝ))) := by
    simpa only [tailConstant,Nat.cast_add,Nat.cast_one] using
      dirichlet_term_bound T h x α M hT hh hα hα' (n+J)
  calc
    _ ≤ ∑' n : Nat, ‖dirichletTerm T h x (n+J)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : Nat, tailConstant T h x α M*((n+J+1:Nat):ℝ)^(-(2*(M:ℝ))) :=
      hn.tsum_le_tsum hb (hps.mul_left _)
    _ = tailConstant T h x α M*(∑' n : Nat, ((n+J+1:Nat):ℝ)^(-(2*(M:ℝ)))) := by
      rw [tsum_mul_left]
    _ ≤ tailConstant T h x α M*((J:ℝ)^(1-2*(M:ℝ))/(2*(M:ℝ)-1)) :=
      mul_le_mul_of_nonneg_left (power_tail (2*(M:ℝ)) hp J hJ) hc
    _ = _ := by ring
lemma finite_dirichlet_error (T h x α : ℝ) (M J : Nat) (hT : 0≤T) (hh : 0<h)
    (hα : 0≤α) (hα' : α<Real.pi/2) (hM : 0<M) (hJ : 0<J) :
    ‖𝓕 (fullWindow T h) x-∑ n ∈ Finset.range J, dirichletTerm T h x n‖ ≤
      tailConstant T h x α M*(J:ℝ)^(1-2*(M:ℝ))/(2*(M:ℝ)-1)+
        2*Real.pi*Real.exp (1/(8*h^2)-T^2/(2*h^2)-Real.pi*x) := by
  have hs := ((dirichlet_norm_summable T h x hh).of_norm).sum_add_tsum_nat_add J
  have he : (∑' n : Nat, dirichletTerm T h x n)-
      (∑ n ∈ Finset.range J, dirichletTerm T h x n)=∑' n : Nat, dirichletTerm T h x (n+J) := by
    rw [←hs]
    ring
  calc
    _ = ‖(𝓕 (fullWindow T h) x-(∑' n : Nat, dirichletTerm T h x n))+
      ((∑' n : Nat, dirichletTerm T h x n)-(∑ n ∈ Finset.range J, dirichletTerm T h x n))‖ := by
      congr 1
      ring
    _ ≤ ‖𝓕 (fullWindow T h) x-(∑' n : Nat, dirichletTerm T h x n)‖+
      ‖(∑' n : Nat, dirichletTerm T h x n)-(∑ n ∈ Finset.range J, dirichletTerm T h x n)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [full_fourier_remainder_norm T h x hh,he,add_comm]
      exact add_le_add (omitted_series_bound T h x α M J hT hh hα hα' hM hJ) le_rfl
end RHHighFiniteDirichlet
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option exponentiation.threshold 20000
open Complex
open scoped FourierTransform
namespace RHHighFiniteDirichletFixed
open RHHighGammaBandwidthTwo RHHighFiniteDirichlet
lemma J_exp : Real.exp (54/5)≤50000 := by
  have hp : Real.exp (54:ℝ)≤(2719/1000:ℝ)^54 := by
    rw [show Real.exp (54:ℝ)=(Real.exp 1)^54 by simpa using Real.exp_nat_mul (1:ℝ) (54:Nat)]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
  have he : Real.exp (54/5)^5=Real.exp (54:ℝ) := by rw [←Real.exp_nat_mul];norm_num
  have hn : (2719/1000:ℝ)^54≤(50000:ℝ)^5 := by norm_num
  have h := hp.trans hn
  rw [←he] at h
  exact le_of_pow_le_pow_left₀ (by decide : (5:Nat)≠0) (by norm_num : (0:ℝ)≤50000) h
lemma tail_bound (T x : ℝ) (hT : 3000000000≤T ∧ T≤3300000000) (hx : 0≤x) :
    tailConstant T 20 x (angle T) 200*(50000:ℝ)^(1-2*(200:ℝ))/(2*(200:ℝ)-1)≤
      Real.exp (-32)/399 := by
  have hc := fixed_constant_tight T hT
  have hp : Real.exp (1:ℝ)≤Real.pi := by linarith [Real.exp_one_lt_d9,Real.pi_gt_three]
  have hp200 : Real.pi^(-(200:ℝ))≤Real.exp (-200) := by
    rw [Real.rpow_neg (by linarith [Real.pi_pos])]
    norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
    have h := pow_le_pow_left₀ (Real.exp_pos _).le hp 200
    rw [←Real.exp_nat_mul] at h
    norm_num only [Nat.cast_ofNat] at h
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) h
  have hj : (50000:ℝ)^(-(399:ℝ))≤Real.exp (-(399*(54/5:ℝ))) := by
    rw [Real.rpow_neg (by norm_num)]
    norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
    have h := pow_le_pow_left₀ (Real.exp_pos _).le J_exp 399
    rw [←Real.exp_nat_mul] at h
    norm_num only [Nat.cast_ofNat] at h
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) h
  have he : Real.exp (4*Real.pi*x*(1/4-(200:ℝ)))≤1 := by
    apply Real.exp_le_one_iff.mpr
    have hpx:0≤Real.pi*x := mul_nonneg Real.pi_pos.le hx
    nlinarith
  have hprod := mul_le_mul (mul_le_mul hc he (Real.exp_pos _).le (by positivity)) hp200
    (by positivity) (by positivity)
  have hall := mul_le_mul hprod hj (by positivity) (by positivity)
  calc
    _ = (boundConstant T 20 (angle T) 200*Real.exp (4*Real.pi*x*(1/4-(200:ℝ)))*
      Real.pi^(-(200:ℝ)))*(50000:ℝ)^(-(399:ℝ))/399 := by unfold tailConstant;norm_num only [Nat.cast_ofNat]
    _ ≤ (Real.exp 4477*1*Real.exp (-200))*Real.exp (-(399*(54/5:ℝ)))/399 :=
      div_le_div_of_nonneg_right hall (by norm_num)
    _ ≤ Real.exp (-32)/399 := by
      simp only [mul_one,←Real.exp_add]
      gcongr
      norm_num
lemma exp32_small : Real.exp (-32)/399≤1/20000000000000000 := by
  have h : (27/10:ℝ)^32≤Real.exp 32 := by
    rw [show Real.exp (32:ℝ)=(Real.exp 1)^32 by simpa using Real.exp_nat_mul (1:ℝ) (32:Nat)]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have hn : (20000000000000000:ℝ)/399≤(27/10:ℝ)^32 := by norm_num
  rw [Real.exp_neg]
  have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<20000000000000000/399) (hn.trans h)
  norm_num [one_div] at hh ⊢
  linarith
lemma pole_bound (T x : ℝ) (hT:3000000000≤T) (hx:0≤x) :
    2*Real.pi*Real.exp (1/3200-T^2/800-Real.pi*x)≤1/20000000000000000 := by
  have he:1/3200-T^2/800-Real.pi*x≤-64 := by
    have hp:0≤Real.pi*x:=mul_nonneg Real.pi_pos.le hx
    nlinarith [sq_nonneg (T-3000000000)]
  have hpow:(2:ℝ)^64≤Real.exp 64 := by
    rw [show Real.exp (64:ℝ)=(Real.exp 1)^64 by simpa using Real.exp_nat_mul (1:ℝ) (64:Nat)]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
  have hsmall:Real.exp (-64)≤1/(2:ℝ)^64 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2^64) hpow
  calc
    _ ≤ 8*Real.exp (-64) := mul_le_mul (by linarith [Real.pi_lt_four])
      (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by norm_num)
    _ ≤ 8*(1/(2:ℝ)^64) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ ≤ _ := by norm_num
lemma finite_error (T x : ℝ) (hT:3000000000≤T ∧ T≤3300000000) (hx:0≤x) :
    ‖𝓕 (RHHighPlattFourier.fullWindow T 20) x-
      ∑ n∈Finset.range 50000,RHHighPlattFourier.dirichletTerm T 20 x n‖≤1/10000000000000000 := by
  have ha:=angle_admissible T hT.1
  have h:=finite_dirichlet_error T 20 x (angle T) 200 50000 (by linarith) (by norm_num)
    ha.1 ha.2 (by norm_num) (by norm_num)
  have ht:tailConstant T 20 x (angle T) 200*(50000:ℝ)^(1-2*(200:ℝ))/(2*(200:ℝ)-1)≤1/20000000000000000 :=
    (tail_bound T x hT hx).trans exp32_small
  have hp:=pole_bound T x hT.1 hx
  norm_num only [show (1/(8*(20:ℝ)^2))=1/3200 by norm_num,
    show (2*(20:ℝ)^2)=800 by norm_num] at h
  exact h.trans (by linarith)
end RHHighFiniteDirichletFixed

end
end RHHighCertifiedFiniteDirichlet
open scoped FourierTransform
theorem solution (T x : ℝ) (hT:3000000000≤T ∧ T≤3300000000) (hx:0≤x) :
 let W:ℝ→ℂ:=fun t=>completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*Complex.I)*
  Complex.exp (((Real.pi*(t+T)/4-t^2/800:ℝ):ℂ))
 ‖𝓕 W x-∑n∈Finset.range 50000,
  Complex.exp (-(1/2+Complex.I*(T:ℂ))*(Real.log ((n+1:ℝ)*Real.sqrt Real.pi):ℂ))*
  𝓕 (RHHighSamplingFunctions.gammaWindow T)
   (x+Real.log ((n+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi))‖≤1/10^16 := by
 have h:=RHHighCertifiedFiniteDirichlet.RHHighFiniteDirichletFixed.finite_error T x hT hx
 have hg:RHHighCertifiedFiniteDirichlet.RHHighGammaFourier.gammaWindow T 20=RHHighSamplingFunctions.gammaWindow T := by
  funext t
  unfold RHHighCertifiedFiniteDirichlet.RHHighGammaFourier.gammaWindow RHHighCertifiedFiniteDirichlet.RHHighGammaFourier.window RHHighSamplingFunctions.gammaWindow
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num]
 have hW:RHHighCertifiedFiniteDirichlet.RHHighPlattFourier.fullWindow T 20=
  (fun t:ℝ=>completedRiemannZeta (1/2+((t+T:ℝ):ℂ)*Complex.I)*
   Complex.exp (((Real.pi*(t+T)/4-t^2/800:ℝ):ℂ))) := by
  funext t
  unfold RHHighCertifiedFiniteDirichlet.RHHighPlattFourier.fullWindow RHHighCertifiedFiniteDirichlet.RHHighGammaFourier.window
  norm_num only [show (2*(20:ℝ)^2)=800 by norm_num]
 rw[hW] at h
 norm_num only [RHHighCertifiedFiniteDirichlet.RHHighPlattFourier.dirichletTerm,
  RHHighCertifiedFiniteDirichlet.RHHighGammaFourier.dirichletWeight,hg] at h ⊢
 exact h
