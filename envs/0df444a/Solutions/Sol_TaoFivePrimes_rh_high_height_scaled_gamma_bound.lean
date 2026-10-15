-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_scaled_gamma_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T11:06:34.227133+00:00
-- url     : https://prove2.me/submissions/a5d76499-ea2e-482a-9238-b25ac19dca7f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
open Complex MeasureTheory Set
open scoped ComplexConjugate
namespace RHHighGamma
lemma quarter_le_four : Real.Gamma (1/4)≤4 := by
  have h := Real.convexOn_Gamma.2
    (by norm_num : (1:ℝ) ∈ Ioi 0) (by norm_num : (2:ℝ) ∈ Ioi 0)
    (by norm_num : 0≤(3/4:ℝ)) (by norm_num : 0≤(1/4:ℝ))
    (by norm_num : (3/4:ℝ)+1/4=1)
  norm_num [smul_eq_mul,Real.Gamma_one,Real.Gamma_two] at h
  have hs := Real.Gamma_add_one (s:=(1/4:ℝ)) (by norm_num)
  norm_num at hs
  nlinarith
lemma norm_beta_le (u v : ℂ) (hu : 0<u.re) (hv : 0<v.re) :
    ‖betaIntegral u v‖ ≤ (betaIntegral (u.re:ℂ) (v.re:ℂ)).re := by
  have h := intervalIntegral.norm_integral_le_integral_norm
    (μ:=volume) (f:=fun x : ℝ => (x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)) (by norm_num : (0:ℝ)≤1)
  unfold betaIntegral
  refine h.trans_eq ?_
  have hi := Complex.reCLM.intervalIntegral_comp_comm
    (Complex.betaIntegral_convergent (u:=(u.re:ℂ)) (v:=(v.re:ℂ))
      (by simpa using hu) (by simpa using hv))
  change (∫ x : ℝ in 0..1, ‖(x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)‖)=_
  change (∫ x : ℝ in 0..1,
    ((x:ℂ)^((u.re:ℂ)-1)*(1-(x:ℂ))^((v.re:ℂ)-1)).re)=
    (∫ x : ℝ in 0..1,
    (x:ℂ)^((u.re:ℂ)-1)*(1-(x:ℂ))^((v.re:ℂ)-1)).re at hi
  rw [←hi]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  have hx0 : 0<x := hx.1
  have hx1 : 0<1-x := by linarith [hx.2]
  have he : 1-(x:ℂ)=((1-x:ℝ):ℂ) := by push_cast; rfl
  dsimp only
  rw [norm_mul,he,Complex.norm_cpow_eq_rpow_re_of_pos hx0,
    Complex.norm_cpow_eq_rpow_re_of_pos hx1]
  have heu : (u.re:ℂ)-1=((u.re-1:ℝ):ℂ) := by push_cast; rfl
  have hev : (v.re:ℂ)-1=((v.re-1:ℝ):ℂ) := by push_cast; rfl
  rw [heu,hev,←Complex.ofReal_cpow hx0.le,←Complex.ofReal_cpow hx1.le,
    ←Complex.ofReal_mul,Complex.ofReal_re]
  simp only [sub_re,one_re]
lemma half_norm_sq (x : ℝ) :
    ‖Complex.Gamma (1/2+(x:ℂ)*I)‖^2=Real.pi/Real.cosh (Real.pi*x) := by
  let z : ℂ := 1/2+(x:ℂ)*I
  have hc : 1-z=conj z := by
    apply Complex.ext <;> simp [z] <;> ring
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hc,Complex.Gamma_conj] at h
  have he : (Real.pi:ℂ)*z=(Real.pi:ℂ)/2+((Real.pi*x:ℝ):ℂ)*I := by
    dsimp [z]; push_cast; ring
  rw [he,Complex.sin_add,Complex.sin_pi_div_two,Complex.cos_pi_div_two,
    one_mul,zero_mul,add_zero,Complex.cos_mul_I,←Complex.ofReal_cosh] at h
  have hn := congrArg norm h
  simp only [norm_mul,Complex.norm_conj,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_pos (Real.cosh_pos (Real.pi*x))] at hn
  simpa only [z,pow_two] using hn
lemma gamma_real_norm {r : ℝ} (hr : 0<r) : ‖Complex.Gamma (r:ℂ)‖=Real.Gamma r := by
  rw [Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.Gamma_pos_of_pos hr)]
lemma quarter_half_ratio (x : ℝ) :
    ‖Complex.Gamma (1/4+(x:ℂ)*I)‖*Real.Gamma (1/2) ≤
      4*‖Complex.Gamma (1/2+(x:ℂ)*I)‖ := by
  let q := Real.Gamma (1/4)
  let h := Real.Gamma (1/2)
  have hq : 0<q := Real.Gamma_pos_of_pos (by norm_num)
  have hh : 0<h := Real.Gamma_pos_of_pos (by norm_num)
  have hB := norm_beta_le (1/4+(x:ℂ)*I) (1/4) (by norm_num) (by norm_num)
  norm_num at hB
  have hr : (betaIntegral (1/4) (1/4)).re=q^2/h := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
    have hq' : Complex.Gamma (1/4:ℂ)=(q:ℂ) := by
      rw [show (1/4:ℂ)=((1/4:ℝ):ℂ) by norm_num,Complex.Gamma_ofReal]
    have hh' : Complex.Gamma (1/2:ℂ)=(h:ℂ) := by
      rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,Complex.Gamma_ofReal]
    rw [show (1/4+1/4:ℂ)=1/2 by ring,hq',hh']
    simp only [←Complex.ofReal_mul,←Complex.ofReal_div,Complex.ofReal_re,pow_two]
  rw [hr] at hB
  have hp := congrArg norm
    (Complex.Gamma_mul_Gamma_eq_betaIntegral (s:=1/4+(x:ℂ)*I) (t:=1/4)
      (by norm_num) (by norm_num))
  have he : (1/4+(x:ℂ)*I)+(1/4)=1/2+(x:ℂ)*I := by ring
  have hn : ‖Complex.Gamma (1/4:ℂ)‖=q := by
    convert gamma_real_norm (by norm_num : (0:ℝ)<1/4) using 1 <;> norm_num
  rw [norm_mul,he,norm_mul,hn] at hp
  have hm : ‖Complex.Gamma (1/4+(x:ℂ)*I)‖*q ≤
      ‖Complex.Gamma (1/2+(x:ℂ)*I)‖*(q^2/h) :=
    hp.trans_le (mul_le_mul_of_nonneg_left hB (norm_nonneg _))
  have hm' := mul_le_mul_of_nonneg_right hm hh.le
  rw [mul_assoc ‖Complex.Gamma (1/2+(x:ℂ)*I)‖,div_mul_cancel₀ _ hh.ne'] at hm'
  have hc : (‖Complex.Gamma (1/4+(x:ℂ)*I)‖*h)*q ≤
      (‖Complex.Gamma (1/2+(x:ℂ)*I)‖*q)*q := by nlinarith [hm']
  have hc' := (mul_le_mul_iff_left₀ hq).mp hc
  exact hc'.trans (by simpa [q,mul_comm] using
    mul_le_mul_of_nonneg_left quarter_le_four (norm_nonneg (Complex.Gamma (1/2+(x:ℂ)*I))))
lemma half_scaled_sq (x : ℝ) :
    (‖Complex.Gamma (1/2+(x:ℂ)*I)‖*Real.exp (Real.pi*x/2))^2≤2*Real.pi := by
  have hc : 0<Real.cosh (Real.pi*x) := Real.cosh_pos _
  have hn : ‖Complex.Gamma (1/2+(x:ℂ)*I)‖^2*Real.cosh (Real.pi*x)=Real.pi :=
    (eq_div_iff hc.ne').mp (half_norm_sq x)
  have he : Real.exp (Real.pi*x)≤2*Real.cosh (Real.pi*x) := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(Real.pi*x))]
  have hs : (Real.exp (Real.pi*x/2))^2=Real.exp (Real.pi*x) := by
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow,hs]
  calc
    _ ≤ ‖Complex.Gamma (1/2+(x:ℂ)*I)‖^2*(2*Real.cosh (Real.pi*x)) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = 2*Real.pi := by nlinarith [hn]
lemma scaled_quarter_le_six (x : ℝ) :
    ‖Complex.Gamma (1/4+(x:ℂ)*I)‖*Real.exp (Real.pi*x/2)≤6 := by
  let U := ‖Complex.Gamma (1/4+(x:ℂ)*I)‖*Real.exp (Real.pi*x/2)
  let V := ‖Complex.Gamma (1/2+(x:ℂ)*I)‖*Real.exp (Real.pi*x/2)
  let H := Real.Gamma (1/2)
  have hU : 0≤U := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hV : 0≤V := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hH : 0<H := Real.Gamma_pos_of_pos (by norm_num)
  have hH2 : H^2=Real.pi := by
    dsimp [H]
    rw [Real.Gamma_one_half_eq,Real.sq_sqrt Real.pi_pos.le]
  have hratio := mul_le_mul_of_nonneg_right (quarter_half_ratio x) (Real.exp_pos (Real.pi*x/2)).le
  have hr : U*H≤4*V := by dsimp [U,H,V]; nlinarith [hratio]
  have hr2 : (U*H)^2≤(4*V)^2 := by gcongr
  have hv2 : V^2≤2*Real.pi := half_scaled_sq x
  have hu2 : U^2*Real.pi≤32*Real.pi := by
    calc
      U^2*Real.pi=(U*H)^2 := by simp only [mul_pow,hH2]
      _ ≤ (4*V)^2 := hr2
      _ ≤ 32*Real.pi := by nlinarith [hv2]
  have hu : U^2≤32 := (mul_le_mul_iff_left₀ Real.pi_pos).mp hu2
  nlinarith [hu]
lemma gaussian_kernel_le (T t h : ℝ) (k : Nat) :
    ‖Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)*
      (Real.exp (Real.pi*(t+T)/4-t^2/(2*h^2)):ℂ)*
      (-2*(Real.pi:ℂ)*I*(t:ℂ))^k‖ ≤
      6*(2*Real.pi*|t|)^k*Real.exp (-t^2/(2*h^2)) := by
  have hg := scaled_quarter_le_six ((t+T)/2)
  rw [show Real.pi*((t+T)/2)/2=Real.pi*(t+T)/4 by ring] at hg
  have hn : ‖-2*(Real.pi:ℂ)*I*(t:ℂ)‖=2*Real.pi*|t| := by
    rw [norm_mul,norm_mul,norm_mul,norm_neg]
    norm_num [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have he : Real.exp (Real.pi*(t+T)/4-t^2/(2*h^2))=
      Real.exp (Real.pi*(t+T)/4)*Real.exp (-t^2/(2*h^2)) := by
    simp only [sub_eq_add_neg,Real.exp_add,neg_div]
  calc
    _ = (‖Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*I)‖*Real.exp (Real.pi*(t+T)/4))*
        ((2*Real.pi*|t|)^k*Real.exp (-t^2/(2*h^2))) := by
      rw [norm_mul,norm_mul,norm_pow,hn,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _),he]
      ring
    _ ≤ 6*((2*Real.pi*|t|)^k*Real.exp (-t^2/(2*h^2))) :=
      mul_le_mul_of_nonneg_right hg (by positivity)
    _ = _ := by ring
end RHHighGamma

 theorem solution :
    (∀ x : ℝ, ‖Complex.Gamma (1/4+(x:ℂ)*Complex.I)‖*Real.exp (Real.pi*x/2)≤6) ∧
    (∀ (T t h : ℝ) (k : Nat),
      ‖Complex.Gamma (1/4+(((t+T)/2:ℝ):ℂ)*Complex.I)*
        (Real.exp (Real.pi*(t+T)/4-t^2/(2*h^2)):ℂ)*
        (-2*(Real.pi:ℂ)*Complex.I*(t:ℂ))^k‖ ≤
        6*(2*Real.pi*|t|)^k*Real.exp (-t^2/(2*h^2))) :=
  ⟨RHHighGamma.scaled_quarter_le_six,RHHighGamma.gaussian_kernel_le⟩
