-- Prove2me | solution 1 for TaoFivePrimes.rh100to1000_xi_coefficient_error
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T05:55:24.491863+00:00
-- url     : https://prove2.me/submissions/b7e2ac4f-2d21-4217-ba55-9ae5387e1d68

import Mathlib
import Definitions.Def_TaoFivePrimes_RH100To1000XiCoefficient
import Theorems.Thm_TaoFivePrimes_rh100to1000_completed_coefficient_error
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RHXiCoefficientAlgebra
open Complex Finset
open RH1000Analytic.CertifiedTaylorQuadrature
lemma shifted_power_derivative (m k : ℕ) (c : ℂ) :
    iteratedDeriv k (fun z : ℂ => (z-c)^m) c=if k=m then (m.factorial:ℂ) else 0 := by
  calc
    _ = iteratedDeriv k (fun z : ℂ => z^m) (c-c) :=
      congrFun (iteratedDeriv_comp_sub_const (n:=k) (f:=fun z : ℂ => z^m) (s:=c)) c
    _ = _ := by simpa only [sub_self,apply_ite,Nat.cast_zero] using (iteratedDeriv_fun_pow_zero (n:=k) (m:=m) (𝕜:=ℂ))
lemma shifted_product_derivative (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c : ℂ) (m n : ℕ) :
    iteratedDeriv n (fun z => (z-c)^m*f z) c=
      if m ≤ n then (n.choose m:ℂ)*(m.factorial:ℂ)*iteratedDeriv (n-m) f c else 0 := by
  have hp : ContDiffAt ℂ n (fun z : ℂ => (z-c)^m) c := by fun_prop
  rw [iteratedDeriv_fun_mul hp hf.contDiff.contDiffAt]
  simp_rw [shifted_power_derivative,mul_ite,ite_mul,mul_zero,zero_mul]
  simp [Finset.sum_ite_eq',Finset.mem_range,Nat.lt_succ_iff]
lemma shifted_product_coefficient (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c : ℂ) (m n : ℕ) :
    coefficient (fun z => (z-c)^m*f z) c n=
      if m ≤ n then coefficient f c (n-m) else 0 := by
  unfold coefficient
  rw [shifted_product_derivative f hf]
  by_cases hm : m ≤ n
  · rw [if_pos hm,if_pos hm]
    have hf1 : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hf2 : ((n-m).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-m)
    have hfac : (n.choose m:ℂ)*(m.factorial:ℂ)*((n-m).factorial:ℂ)=(n.factorial:ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
    field_simp
    rw [←hfac]
    ring
  · simp [hm]
lemma coefficient_add (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (n : ℕ) : coefficient (f+g) c n=coefficient f c n+coefficient g c n := by
  unfold coefficient
  rw [iteratedDeriv_add hf.contDiff.contDiffAt hg.contDiff.contDiffAt,add_div]
lemma coefficient_const_mul (A : ℂ) (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coefficient (fun z => A*f z) c n=A*coefficient f c n := by
  unfold coefficient
  rw [iteratedDeriv_const_mul_field]
  ring
lemma coefficient_const (A c : ℂ) (n : ℕ) :
    coefficient (fun _ : ℂ => A) c n=if n=0 then A else 0 := by
  cases n <;> simp [coefficient,iteratedDeriv_const]
end RHXiCoefficientAlgebra

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RHXiCoefficientAlgebra
open Complex
open RH1000Analytic.CertifiedTaylorQuadrature
noncomputable def transform (f : ℂ → ℂ) (z : ℂ) : ℂ := 1/2+z*(z-1)/2*f z
lemma transform_coefficient (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) (n : ℕ) :
    coefficient (transform f) c n=
      (if n=0 then (1/2:ℂ) else 0)+c*(c-1)/2*coefficient f c n+
      (2*c-1)/2*(if 1 ≤ n then coefficient f c (n-1) else 0)+
      (1/2:ℂ)*(if 2 ≤ n then coefficient f c (n-2) else 0) := by
  let g0 : ℂ → ℂ := fun _ => 1/2
  let g1 : ℂ → ℂ := fun z => c*(c-1)/2*f z
  let g2 : ℂ → ℂ := fun z => (2*c-1)/2*((z-c)^1*f z)
  let g3 : ℂ → ℂ := fun z => (1/2:ℂ)*((z-c)^2*f z)
  have h0 : Differentiable ℂ g0 := by dsimp [g0]; fun_prop
  have h1 : Differentiable ℂ g1 := by dsimp [g1]; fun_prop
  have h2 : Differentiable ℂ g2 := by dsimp [g2]; fun_prop
  have h3 : Differentiable ℂ g3 := by dsimp [g3]; fun_prop
  have he : transform f=g0+g1+g2+g3 := by
    funext z
    simp only [transform,g0,g1,g2,g3,Pi.add_apply,pow_one]
    ring
  rw [he,coefficient_add (g0+g1+g2) g3 ((h0.add h1).add h2) h3,
    coefficient_add (g0+g1) g2 (h0.add h1) h2,coefficient_add g0 g1 h0 h1]
  dsimp only [g0,g1,g2,g3]
  rw [coefficient_const,coefficient_const_mul,coefficient_const_mul,
    coefficient_const_mul,shifted_product_coefficient f hf,shifted_product_coefficient f hf]
end RHXiCoefficientAlgebra

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RHXiCoefficientAlgebra
open Complex
noncomputable def template (A B : ℂ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (if n=0 then (1/2:ℂ) else 0)+A*f n+
    B*(if 1 ≤ n then f (n-1) else 0)+(1/2:ℂ)*(if 2 ≤ n then f (n-2) else 0)
lemma shift_error (f g : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ n, ‖f n-g n‖ ≤ ε) (m n : ℕ) :
    ‖(if m ≤ n then f (n-m) else 0)-(if m ≤ n then g (n-m) else 0)‖ ≤ ε := by
  by_cases hm : m ≤ n
  · simpa only [if_pos hm] using h (n-m)
  · simp only [if_neg hm,sub_self,norm_zero]
    exact hε
lemma template_error (A B : ℂ) (f g : ℕ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ n, ‖f n-g n‖ ≤ ε) (n : ℕ) :
    ‖template A B f n-template A B g n‖ ≤ (‖A‖+‖B‖+1/2)*ε := by
  have he : template A B f n-template A B g n=
      A*(f n-g n)+B*((if 1 ≤ n then f (n-1) else 0)-(if 1 ≤ n then g (n-1) else 0))+
      (1/2:ℂ)*((if 2 ≤ n then f (n-2) else 0)-(if 2 ≤ n then g (n-2) else 0)) := by
    unfold template
    ring
  rw [he]
  have h1 := shift_error f g ε hε h 1 n
  have h2 := shift_error f g ε hε h 2 n
  calc
    _ ≤ ‖A*(f n-g n)+B*((if 1 ≤ n then f (n-1) else 0)-(if 1 ≤ n then g (n-1) else 0))‖+
      ‖(1/2:ℂ)*((if 2 ≤ n then f (n-2) else 0)-(if 2 ≤ n then g (n-2) else 0))‖ := norm_add_le _ _
    _ ≤ ‖A*(f n-g n)‖+‖B*((if 1 ≤ n then f (n-1) else 0)-(if 1 ≤ n then g (n-1) else 0))‖+
      ‖(1/2:ℂ)*((if 2 ≤ n then f (n-2) else 0)-(if 2 ≤ n then g (n-2) else 0))‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖A‖*ε+‖B‖*ε+(1/2:ℝ)*ε := by
      simp only [norm_mul]
      norm_num only [norm_div,norm_one,norm_ofNat]
      gcongr
      exact h n
    _ = _ := by ring
end RHXiCoefficientAlgebra

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHXiCoefficientAlgebra
open Complex
lemma center_bound (T : ℝ) (hT : |T| ≤ 1000) :
    ‖RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1001 := by
  have h := Complex.norm_le_abs_re_add_abs_im (RH1000Analytic.CertifiedLocalXi.center T)
  norm_num [RH1000Analytic.CertifiedLocalXi.center] at h ⊢
  linarith
lemma center_sub_one_bound (T : ℝ) (hT : |T| ≤ 1000) :
    ‖RH1000Analytic.CertifiedLocalXi.center T-1‖ ≤ 1001 := by
  have h := Complex.norm_le_abs_re_add_abs_im (RH1000Analytic.CertifiedLocalXi.center T-1)
  norm_num [RH1000Analytic.CertifiedLocalXi.center] at h ⊢
  linarith
lemma quadratic_factor_bound (T : ℝ) (hT : |T| ≤ 1000) :
    ‖RH1000Analytic.CertifiedLocalXi.center T*(RH1000Analytic.CertifiedLocalXi.center T-1)/2‖ ≤ 502000 := by
  rw [norm_div,norm_mul]
  norm_num only [norm_ofNat]
  calc
    _ ≤ (1001:ℝ)*1001/2 := by gcongr; exact center_bound T hT; exact center_sub_one_bound T hT
    _ ≤ _ := by norm_num
lemma linear_factor_bound (T : ℝ) (hT : |T| ≤ 1000) :
    ‖(2*RH1000Analytic.CertifiedLocalXi.center T-1)/2‖ ≤ 1002 := by
  rw [norm_div]
  norm_num only [norm_ofNat]
  have h := norm_sub_le (2*RH1000Analytic.CertifiedLocalXi.center T) (1:ℂ)
  rw [norm_mul] at h
  norm_num only [norm_ofNat,norm_one] at h
  calc
    _ ≤ (2*‖RH1000Analytic.CertifiedLocalXi.center T‖+1)/2 := by gcongr
    _ ≤ (2*1001+1:ℝ)/2 := by gcongr; exact center_bound T hT
    _ ≤ _ := by norm_num
end RHXiCoefficientAlgebra

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
namespace RHXiCoefficientAlgebra
open Complex
open RH1000Analytic.CertifiedTaylorQuadrature
lemma xi_coefficient_error (T : ℝ) (hT : |T| ≤ 1000) (n : ℕ) :
    ‖coefficient RH1000Analytic.CertifiedLocalXi.xi (RH1000Analytic.CertifiedLocalXi.center T) n-
      TaoFivePrimes_RH100To1000XiCoefficient T n‖ ≤ 1/10^359 := by
  let c := RH1000Analytic.CertifiedLocalXi.center T
  let A := c*(c-1)/2
  let B := (2*c-1)/2
  let f : ℕ → ℂ := coefficient completedRiemannZeta₀ c
  let g : ℕ → ℂ := TaoFivePrimes_RH100To1000CompletedZetaCoefficient T
  have h : ∀ j, ‖f j-g j‖ ≤ (1/10^365:ℝ) :=
    fun j => TaoFivePrimes.rh100to1000_completed_coefficient_error T hT j
  have hform : coefficient RH1000Analytic.CertifiedLocalXi.xi c n=template A B f n := by
    have hx : RH1000Analytic.CertifiedLocalXi.xi=transform completedRiemannZeta₀ := rfl
    rw [hx,transform_coefficient _ differentiable_completedZeta₀]
    rfl
  have hmodel : TaoFivePrimes_RH100To1000XiCoefficient T n=template A B g n := rfl
  rw [hform,hmodel]
  have he := template_error A B f g (1/10^365) (by positivity) h n
  apply he.trans
  have ha : ‖A‖ ≤ 502000 := quadratic_factor_bound T hT
  have hb : ‖B‖ ≤ 1002 := linear_factor_bound T hT
  calc
    _ ≤ (502000+1002+1/2:ℝ)*(1/10^365) := by gcongr
    _ ≤ (10:ℝ)^6*(1/10^365) := by gcongr; norm_num
    _ = _ := by norm_num
end RHXiCoefficientAlgebra

theorem solution (T : ℝ) (hT : |T| ≤ 1000) (n : ℕ) :
    ‖RH1000Analytic.CertifiedTaylorQuadrature.coefficient RH1000Analytic.CertifiedLocalXi.xi
      (RH1000Analytic.CertifiedLocalXi.center T) n-
      TaoFivePrimes_RH100To1000XiCoefficient T n‖ ≤ 1/10^359 := RHXiCoefficientAlgebra.xi_coefficient_error T hT n
