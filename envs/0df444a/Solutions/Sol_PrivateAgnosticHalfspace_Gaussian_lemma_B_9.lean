-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.lemma_B_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:02:36.586447+00:00
-- url     : https://prove2.me/submissions/afa529ed-4377-4d54-a982-5fc0fd0ed359

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Mathlib
open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def hermiteComplex (n : ℕ) : Polynomial ℂ :=
  (Polynomial.hermite n).map (Int.castRingHom ℂ)

lemma hermiteComplex_succ (n : ℕ) :
    hermiteComplex (n + 1) = Polynomial.X * hermiteComplex n - (hermiteComplex n).derivative := by
  simp only [hermiteComplex, Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.derivative_map]

lemma generating_derivative (x : ℂ) (n : ℕ) (t : ℂ) :
    HasDerivAt (fun z => (hermiteComplex n).eval (x - z) * Complex.exp (z * x - z ^ 2 / 2))
      ((hermiteComplex (n + 1)).eval (x - t) * Complex.exp (t * x - t ^ 2 / 2)) t := by
  have hp := ((hermiteComplex n).hasDerivAt (x - t)).comp t ((hasDerivAt_const t x).sub (hasDerivAt_id t))
  have he := ((((hasDerivAt_id t).mul_const x).sub (((hasDerivAt_id t).pow 2).div_const 2))).cexp
  have hh := hp.mul he
  convert! hh using 1
  rw [hermiteComplex_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Function.comp_apply, Pi.sub_apply, Pi.pow_apply, id_eq, Nat.reduceSub, pow_one]
  ring

lemma iteratedDeriv_generating (x : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => Complex.exp (z * x - z ^ 2 / 2)) =
      fun t => (hermiteComplex n).eval (x - t) * Complex.exp (t * x - t ^ 2 / 2) := by
  induction n with
  | zero =>
    funext t
    simp [hermiteComplex, Polynomial.hermite_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (generating_derivative x n t).deriv

lemma hermite_generating_complex (x t : ℂ) :
    HasSum (fun n : ℕ => (hermiteComplex n).eval x * t ^ n / n.factorial)
      (Complex.exp (t * x - t ^ 2 / 2)) := by
  have hf : Differentiable ℂ (fun z : ℂ => Complex.exp (z * x - z ^ 2 / 2)) := by fun_prop
  have hh := Complex.hasSum_taylorSeries_of_entire hf 0 t
  simp only [iteratedDeriv_generating, sub_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, sub_self, Complex.exp_zero, mul_one, smul_eq_mul] at hh
  convert! hh using 1
  funext n
  ring

end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma hermiteComplex_eval_real (n : ℕ) (x : ℝ) :
    (hermiteComplex n).eval (x : ℂ) =
      ((((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval x : ℝ) : ℂ) := by
  have hm : Int.castRingHom ℂ = Complex.ofRealHom.comp (Int.castRingHom ℝ) := by
    ext z
    simp
  change (hermiteComplex n).eval (Complex.ofRealHom x) = _
  rw [hermiteComplex, hm, ← Polynomial.map_map, Polynomial.eval_map_apply]
  rfl

lemma hermite_generating_real (x t : ℝ) :
    HasSum (fun n : ℕ => AMPLowDeg.RankOne.hermNorm n x * t ^ n / Real.sqrt (n.factorial))
      (Real.exp (t * x - t ^ 2 / 2)) := by
  have hh := Complex.hasSum_re (hermite_generating_complex (x : ℂ) (t : ℂ))
  simp only [hermiteComplex_eval_real, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_exp, Complex.ofReal_re] at hh
  convert! hh using 1
  funext n
  unfold AMPLowDeg.RankOne.hermNorm
  rw [div_mul_eq_mul_div, div_div, Real.mul_self_sqrt (Nat.cast_nonneg _)]
end PrivateAgnosticHalfspace.Gaussian
open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian

lemma iteratedDeriv_mul_power_zero (f : ℂ → ℂ) (n k : ℕ) (hf : ContDiffAt ℂ n f 0) :
    iteratedDeriv n (fun z => z ^ k * f z) 0 =
      if k ≤ n then (n.choose k : ℂ) * k.factorial * iteratedDeriv (n-k) f 0 else 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf]
  simp only [iteratedDeriv_fun_pow_zero]
  by_cases h : k ≤ n
  · rw [if_pos h, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hk
      exact False.elim (hk (Finset.mem_range.mpr (by omega)))
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    have hik : i ≠ k := by have := Finset.mem_range.mp hi; omega
    simp [hik]

noncomputable def mehlerKernelComplex (x y z : ℂ) : ℂ :=
  Complex.exp (-(1 / 2 : ℂ) * Complex.log (1-z^2) +
    (2*z*x*y-z^2*(x^2+y^2))/(2*(1-z^2)))

lemma mehler_rightHalfPlane (z : ℂ) (hz : ‖z‖ < 1) : 0 < (1-z^2).re := by
  have h := Complex.abs_re_le_norm (z^2)
  have hn : ‖z^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  simp only [Complex.sub_re,Complex.one_re]
  have := le_abs_self (z^2).re
  linarith

lemma mehlerKernel_differentiableOn (x y : ℂ) :
    DifferentiableOn ℂ (mehlerKernelComplex x y) (Metric.ball 0 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball,dist_zero_right] using hz
  have hr := mehler_rightHalfPlane z hz'
  have hne : (1-z^2) ≠ 0 := by intro h; rw [h] at hr; norm_num at hr
  have hlog := ((Complex.hasDerivAt_log (Or.inl hr)).comp z
    ((hasDerivAt_const z (1:ℂ)).sub ((hasDerivAt_id z).pow 2))).differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  exact ((hlog.const_mul _).add
    ((((differentiableAt_const (c := (2:ℂ))).mul differentiableAt_id).mul_const x |>.mul_const y).sub
      ((differentiableAt_id.pow 2).mul_const (x^2+y^2)) |>.div
      ((differentiableAt_const (c := (2:ℂ))).mul ((differentiableAt_const (c := (1:ℂ))).sub
        (differentiableAt_id.pow 2))) (mul_ne_zero (by norm_num) hne))).cexp

end PrivateAgnosticHalfspace.Gaussian

namespace PrivateAgnosticHalfspace.Gaussian
lemma derivative_hermiteComplex (n : ℕ) :
    derivative (hermiteComplex (n+1)) = Polynomial.C ((n : ℂ)+1) * hermiteComplex n := by
  induction n with
  | zero => simp [hermiteComplex]
  | succ n ih =>
    have key : derivative (hermiteComplex (n+1+1)) =
        hermiteComplex (n+1) + Polynomial.C ((n : ℂ)+1) *
          (Polynomial.X * hermiteComplex n - derivative (hermiteComplex n)) := by
      rw [hermiteComplex_succ (n+1),derivative_sub,derivative_mul,derivative_X,ih,derivative_C_mul]
      ring
    have hC : (Polynomial.C (((n : ℂ)+1)+1) : Polynomial ℂ) = Polynomial.C ((n : ℂ)+1)+1 := by
      rw [map_add,map_one]
    rw [key,←hermiteComplex_succ n]
    push_cast
    rw [hC]
    ring

lemma hermiteComplex_recur (n : ℕ) (x : ℂ) :
    (hermiteComplex (n+2)).eval x = x * (hermiteComplex (n+1)).eval x -
      (n+1 : ℂ) * (hermiteComplex n).eval x := by
  rw [show n+2=n+1+1 by omega,hermiteComplex_succ,derivative_hermiteComplex]
  simp

lemma hermite_product_recurrence (n : ℕ) (x y : ℂ) :
    (hermiteComplex (n+4)).eval x * (hermiteComplex (n+4)).eval y =
      x*y*((hermiteComplex (n+3)).eval x * (hermiteComplex (n+3)).eval y) +
      (n+3 : ℂ)*(2*n+5-x^2-y^2)*((hermiteComplex (n+2)).eval x * (hermiteComplex (n+2)).eval y) +
      (n+3 : ℂ)*(n+2)*x*y*((hermiteComplex (n+1)).eval x * (hermiteComplex (n+1)).eval y) -
      (n+3 : ℂ)*(n+2)*(n+1)^2*((hermiteComplex n).eval x * (hermiteComplex n).eval y) := by
  have h4 (z : ℂ) := hermiteComplex_recur (n+2) z
  have h3 (z : ℂ) := hermiteComplex_recur (n+1) z
  have h2 (z : ℂ) := hermiteComplex_recur n z
  simp only [Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_ofNat] at h4 h3 h2
  rw [h4 x,h4 y,h3 x,h3 y,h2 x,h2 y]
  ring

lemma mehlerKernel_hasDerivAt (x y z : ℂ) (hz : ‖z‖ < 1) :
    HasDerivAt (mehlerKernelComplex x y)
      (mehlerKernelComplex x y z *
        ((x*y+z*(1-x^2-y^2)+x*y*z^2-z^3)/(1-z^2)^2)) z := by
  have hr := mehler_rightHalfPlane z hz
  have hne : 1-z^2 ≠ 0 := by intro h; rw [h] at hr; norm_num at hr
  have hq : HasDerivAt (fun w : ℂ => 1-w^2) (-2*z) z := by
    convert! (hasDerivAt_const z (1:ℂ)).sub ((hasDerivAt_id z).pow 2) using 1 <;> simp only [id_eq] <;> ring
  have hn : HasDerivAt (fun w : ℂ => 2*w*x*y-w^2*(x^2+y^2))
      (2*x*y-2*z*(x^2+y^2)) z := by
    convert! (((hasDerivAt_id z).const_mul 2 |>.mul_const x |>.mul_const y).sub
      (((hasDerivAt_id z).pow 2).mul_const (x^2+y^2))) using 1 <;> simp only [id_eq] <;> ring
  have h := ((((Complex.hasDerivAt_log (Or.inl hr)).comp z hq).const_mul (-(1/2:ℂ))).add
    (hn.div (hq.const_mul 2) (mul_ne_zero (by norm_num) hne))).cexp
  convert! h using 1
  unfold mehlerKernelComplex
  congr 1
  field_simp
  ring
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma iteratedDeriv_mul_power_zero' (f : ℂ → ℂ) (n k : ℕ) (hf : ContDiffAt ℂ n f 0) :
    iteratedDeriv n (fun z => z ^ k * f z) 0 =
      (n.descFactorial k : ℂ) * iteratedDeriv (n-k) f 0 := by
  rw [iteratedDeriv_mul_power_zero f n k hf]
  by_cases h : k ≤ n
  · rw [if_pos h,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
    ring
  · rw [if_neg h,Nat.descFactorial_eq_zero_iff_lt.mpr (by omega),Nat.cast_zero,zero_mul]

lemma mehlerKernel_ode (x y z : ℂ) (hz : ‖z‖ < 1) :
    deriv (mehlerKernelComplex x y) z - 2 * (z^2 * deriv (mehlerKernelComplex x y) z) +
      z^4 * deriv (mehlerKernelComplex x y) z =
    x*y * mehlerKernelComplex x y z + (1-x^2-y^2) * (z * mehlerKernelComplex x y z) +
      x*y * (z^2 * mehlerKernelComplex x y z) - z^3 * mehlerKernelComplex x y z := by
  rw [(mehlerKernel_hasDerivAt x y z hz).deriv]
  have hne : 1-z^2 ≠ 0 := by
    have h := mehler_rightHalfPlane z hz
    intro he; rw [he] at h; norm_num at h
  field_simp
  ring

lemma mehlerKernel_contDiffAt (x y : ℂ) (n : ℕ) :
    ContDiffAt ℂ n (mehlerKernelComplex x y) 0 :=
  ((mehlerKernel_differentiableOn x y).analyticAt (Metric.ball_mem_nhds 0 (by norm_num))).contDiffAt

lemma mehlerKernel_deriv_contDiffAt (x y : ℂ) (n : ℕ) :
    ContDiffAt ℂ n (deriv (mehlerKernelComplex x y)) 0 :=
  (mehlerKernel_contDiffAt x y (n+1)).derivWithin (by simp)
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma iteratedDeriv_polynomial_mul (f : ℂ → ℂ) (n : ℕ) (hf : ContDiffAt ℂ n f 0)
    {l : ℕ} (a : Fin l → ℂ) :
    iteratedDeriv n (fun z => ∑ i : Fin l, a i * (z ^ i.val * f z)) 0 =
      ∑ i : Fin l, a i * ((n.descFactorial i.val : ℂ) * iteratedDeriv (n-i.val) f 0) := by
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  simp only [iteratedDeriv_const_mul_field,iteratedDeriv_mul_power_zero' _ _ _ hf]

lemma mehlerKernel_derivative_relation (x y : ℂ) (n : ℕ) :
    (∑ i : Fin 5, (![1,0,-2,0,1] : Fin 5 → ℂ) i *
      ((n.descFactorial i.val : ℂ) * iteratedDeriv (n-i.val+1) (mehlerKernelComplex x y) 0)) =
    ∑ i : Fin 4, (![x*y,1-x^2-y^2,x*y,-1] : Fin 4 → ℂ) i *
      ((n.descFactorial i.val : ℂ) * iteratedDeriv (n-i.val) (mehlerKernelComplex x y) 0) := by
  let f := mehlerKernelComplex x y
  let Q : Fin 5 → ℂ := ![1,0,-2,0,1]
  let P : Fin 4 → ℂ := ![x*y,1-x^2-y^2,x*y,-1]
  have he : (fun z => ∑ i : Fin 5, Q i * (z^i.val * deriv f z)) =ᶠ[nhds 0]
      (fun z => ∑ i : Fin 4, P i * (z^i.val * f z)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball,dist_zero_right] using hz
    simpa [Q,P,f,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using mehlerKernel_ode x y z hz'
  have hid := he.iteratedDeriv_eq n
  rw [iteratedDeriv_polynomial_mul _ _ (mehlerKernel_deriv_contDiffAt x y n),
    iteratedDeriv_polynomial_mul _ _ (mehlerKernel_contDiffAt x y n)] at hid
  simpa only [f,Q,P,← iteratedDeriv_succ'] using hid

lemma mehlerKernel_derivative_recurrence (x y : ℂ) (n : ℕ) :
    iteratedDeriv (n+4) (mehlerKernelComplex x y) 0 =
      x*y*iteratedDeriv (n+3) (mehlerKernelComplex x y) 0 +
      (n+3 : ℂ)*(2*n+5-x^2-y^2)*iteratedDeriv (n+2) (mehlerKernelComplex x y) 0 +
      (n+3 : ℂ)*(n+2)*x*y*iteratedDeriv (n+1) (mehlerKernelComplex x y) 0 -
      (n+3 : ℂ)*(n+2)*(n+1)^2*iteratedDeriv n (mehlerKernelComplex x y) 0 := by
  have hid := mehlerKernel_derivative_relation x y (n+3)
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.val_eq_zero,Nat.zero_add,zero_mul,one_mul,neg_mul,zero_add,add_zero,
    Nat.sub_zero,Nat.descFactorial_zero,Nat.cast_one,Nat.descFactorial_one] at hid
  have h1 : n+3-1=n+2 := by omega
  have h2 : n+3-2=n+1 := by omega
  have h3 : n+3-3=n := by omega
  simp only [Nat.reduceAdd,Fin.sum_univ_zero,add_zero] at hid
  simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.mul_one,h1,h2,h3,
    Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] at hid
  cases n with
  | zero => norm_num at hid ⊢; linear_combination hid
  | succ n =>
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.add_sub_cancel_left,
      Nat.add_assoc,Nat.reduceAdd] at hid ⊢
    norm_num at hid
    push_cast at hid ⊢
    linear_combination hid
end PrivateAgnosticHalfspace.Gaussian
namespace PrivateAgnosticHalfspace.Gaussian
lemma mehlerKernel_zero (x y : ℂ) : mehlerKernelComplex x y 0 = 1 := by
  simp [mehlerKernelComplex]

lemma hermiteComplex_low (x : ℂ) :
    (hermiteComplex 0).eval x = 1 ∧ (hermiteComplex 1).eval x = x ∧
    (hermiteComplex 2).eval x = x^2-1 ∧ (hermiteComplex 3).eval x = x^3-3*x := by
  have h0 : (hermiteComplex 0).eval x = 1 := by simp [hermiteComplex]
  have h1 : (hermiteComplex 1).eval x = x := by simp [hermiteComplex]
  have h2 := hermiteComplex_recur 0 x
  have h3 := hermiteComplex_recur 1 x
  norm_num at h2 h3
  rw [h0,h1] at h2
  rw [h2,h1] at h3
  exact ⟨h0,h1,by linear_combination h2,by linear_combination h3⟩

lemma mehlerKernel_iteratedDeriv_zero (x y : ℂ) (n : ℕ) :
    iteratedDeriv n (mehlerKernelComplex x y) 0 = (hermiteComplex n).eval x * (hermiteComplex n).eval y := by
  have h0 : iteratedDeriv 0 (mehlerKernelComplex x y) 0 = 1 := by
    rw [iteratedDeriv_zero,mehlerKernel_zero]
  have h1 := mehlerKernel_derivative_relation x y 0
  have h2 := mehlerKernel_derivative_relation x y 1
  have h3 := mehlerKernel_derivative_relation x y 2
  norm_num [Fin.sum_univ_succ,h0] at h1 h2 h3
  rw [h1] at h2 h3
  rw [h2] at h3
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · interval_cases n
      · rw [h0,(hermiteComplex_low x).1,(hermiteComplex_low y).1]; ring
      · rw [iteratedDeriv_one,(hermiteComplex_low x).2.1,(hermiteComplex_low y).2.1]; exact h1
      · rw [(hermiteComplex_low x).2.2.1,(hermiteComplex_low y).2.2.1]
        linear_combination h2
      · rw [(hermiteComplex_low x).2.2.2,(hermiteComplex_low y).2.2.2]
        linear_combination h3
    · obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le (by omega : 4 ≤ n)
      subst n
      rw [Nat.add_comm 4 m]
      rw [mehlerKernel_derivative_recurrence]
      rw [ih (m+3) (by omega),ih (m+2) (by omega),ih (m+1) (by omega),ih m (by omega)]
      exact (hermite_product_recurrence m x y).symm

lemma mehler_hasSum_complex (x y z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z^n * (hermiteComplex n).eval x * (hermiteComplex n).eval y / n.factorial)
      (mehlerKernelComplex x y z) := by
  have hh := Complex.hasSum_taylorSeries_on_ball (mehlerKernel_differentiableOn x y)
    (show z ∈ Metric.ball 0 1 by simpa [Metric.mem_ball,dist_zero_right] using hz)
  simp only [sub_zero,mehlerKernel_iteratedDeriv_zero,smul_eq_mul] at hh
  convert! hh using 1
  funext n; ring
end PrivateAgnosticHalfspace.Gaussian
open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma mehlerKernelComplex_real (x y ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) :
    mehlerKernelComplex x y ρ =
      (((1-ρ^2) ^ (-(1 : ℝ)/2) * Real.exp ((2*ρ*x*y-ρ^2*(x^2+y^2))/(2*(1-ρ^2))) : ℝ) : ℂ) := by
  have hp : 0 < 1-ρ^2 := by nlinarith [hρ.1,hρ.2]
  unfold mehlerKernelComplex
  have he : -(1/2 : ℂ)*Complex.log (1-(ρ:ℂ)^2) +
      (2*(ρ:ℂ)*x*y-(ρ:ℂ)^2*((x:ℂ)^2+(y:ℂ)^2))/(2*(1-(ρ:ℂ)^2)) =
      ((Real.log (1-ρ^2)*(-(1 : ℝ)/2) +
        (2*ρ*x*y-ρ^2*(x^2+y^2))/(2*(1-ρ^2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_log hp.le]
    push_cast
    ring
  rw [he,← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos hp,← Real.exp_add]

lemma mehler_hasSum_real (x y ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) :
    HasSum (fun n : ℕ => ρ^n * AMPLowDeg.RankOne.hermNorm n x * AMPLowDeg.RankOne.hermNorm n y)
      ((1-ρ^2) ^ (-(1 : ℝ)/2) * Real.exp ((2*ρ*x*y-ρ^2*(x^2+y^2))/(2*(1-ρ^2)))) := by
  have hh := Complex.hasSum_re (mehler_hasSum_complex x y ρ
    (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_lt] using hρ))
  rw [mehlerKernelComplex_real x y ρ hρ,Complex.ofReal_re] at hh
  simp only [hermiteComplex_eval_real,← Complex.ofReal_pow,← Complex.ofReal_mul,
    ← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.ofReal_re] at hh
  convert! hh using 1
  funext n
  unfold AMPLowDeg.RankOne.hermNorm
  have hsq : Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ) = n.factorial :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  calc
    _ = (ρ^n * ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval x *
      ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval y) /
      (Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) := by ring
    _ = _ := by rw [hsq]
end PrivateAgnosticHalfspace.Gaussian
set_option autoImplicit false
open scoped BigOperators
lemma real_product_summable {A B : Type*} (f : A → ℝ) (g : B → ℝ)
    (hf : Summable f) (hg : Summable g) : Summable (fun p : A × B => f p.1 * g p.2) := by
  exact summable_mul_of_summable_norm hf.norm hg.norm
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma hasSum_fin_product {Y : Type*} {n : ℕ} (f : Fin n → Y → ℝ) (a : Fin n → ℝ)
    (hf : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun y : Fin n → Y => ∏ i, f i (y i)) (∏ i, a i) := by
  induction n with
  | zero => simpa using (hasSum_fintype (fun y : Fin 0 → Y => ∏ i, f i (y i)))
  | succ n ih =>
    have htail := ih (fun i : Fin n => f i.succ) (fun i => a i.succ) (fun i => hf i.succ)
    let g : (Fin n → Y) → ℝ := fun y => ∏ i : Fin n, f i.succ (y i)
    have htail' : HasSum g (∏ i : Fin n, a i.succ) := htail
    have hs := real_product_summable (f 0) g (hf 0).summable htail'.summable
    have hh := (hf 0).mul htail' hs
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Y)).hasSum_iff]
    simpa only [g,Function.comp_def,Fin.consEquiv_apply,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ] using hh
end PrivateAgnosticHalfspace.Gaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma product_mehler_values (d : ℕ) (x y : Vec d) (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) :
    (∏ i : Fin d, (1-ρ^2)^(-(1:ℝ)/2) *
      Real.exp ((2*ρ*x i*y i-ρ^2*((x i)^2+(y i)^2))/(2*(1-ρ^2)))) =
      (1-ρ^2)^(-(d:ℝ)/2) *
      Real.exp ((2*ρ*inner ℝ x y-ρ^2*(‖x‖^2+‖y‖^2))/(2*(1-ρ^2))) := by
  have hp : 0 < 1-ρ^2 := by nlinarith [hρ.1,hρ.2]
  have hin : inner ℝ x y = ∑ i, x i*y i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]
  have hsum : (∑ i : Fin d, (2*ρ*x i*y i-ρ^2*((x i)^2+(y i)^2))/(2*(1-ρ^2))) =
      (2*ρ*inner ℝ x y-ρ^2*(‖x‖^2+‖y‖^2))/(2*(1-ρ^2)) := by
    rw [← Finset.sum_div,hin,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    congr 1
    simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _; ring
  simp_rw [Real.rpow_def_of_pos hp,← Real.exp_add]
  rw [← Real.exp_sum,Finset.sum_add_distrib,hsum]
  congr 1
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring
end PrivateAgnosticHalfspace.Gaussian

open PrivateAgnosticHalfspace.Gaussian in
theorem solution (d : ℕ) (x y : Vec d) (ρ : ℝ) (hρ : -1 < ρ ∧ ρ < 1) :
    HasSum (fun κ : Fin d → ℕ => ρ ^ degree κ * hermite d κ x * hermite d κ y)
      ((1 - ρ ^ 2) ^ (-(d : ℝ) / 2) *
        Real.exp ((2 * ρ * inner ℝ x y - ρ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) /
          (2 * (1 - ρ ^ 2)))) := by
  have hh := hasSum_fin_product
    (fun i : Fin d => fun n : ℕ => ρ^n * AMPLowDeg.RankOne.hermNorm n (x i) *
      AMPLowDeg.RankOne.hermNorm n (y i))
    (fun i : Fin d => (1-ρ^2)^(-(1:ℝ)/2) *
      Real.exp ((2*ρ*x i*y i-ρ^2*((x i)^2+(y i)^2))/(2*(1-ρ^2))))
    (fun i => mehler_hasSum_real (x i) (y i) ρ hρ)
  rw [product_mehler_values d x y ρ hρ] at hh
  convert! hh using 1
  funext κ
  simp only [PrivateAgnosticHalfspace.Gaussian.hermite,PrivateAgnosticHalfspace.Gaussian.degree,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
