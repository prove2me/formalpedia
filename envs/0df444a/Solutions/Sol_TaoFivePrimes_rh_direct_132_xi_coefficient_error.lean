-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_xi_coefficient_error
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:13:39.198685+00:00
-- url     : https://prove2.me/submissions/17f741c8-53d6-4a95-a324-0c874257c957

import Definitions.Def_TaoFivePrimes_RHDirect132XiCoefficients
import Theorems.Thm_TaoFivePrimes_rh_direct_132_completed_zeta_coefficients
import Definitions.Def_TaoFivePrimes_RH100To1000LocalAnalyticModel
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex Finset
open RH1000Analytic.CertifiedTaylorQuadrature

namespace DirectXi132CoefficientIdentity

noncomputable def q (z : ℂ) : ℂ := z*(z-1)/2
noncomputable def center : ℂ := RH1000Analytic.CertifiedLocalXi.center 132
noncomputable def lambda (n : ℕ) : ℂ := coefficient completedRiemannZeta₀ center n

lemma coefficient_mul (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z*g z) c n =
      ∑ m ∈ range (n+1), coefficient f c m * coefficient g c (n-m) := by
  unfold coefficient
  rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hg.contDiff.contDiffAt,sum_div]
  apply sum_congr rfl
  intro m hm
  have hmn : m≤n := by simpa using mem_range.mp hm
  rw [Nat.cast_choose ℂ hmn]
  have h0 : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  have h1 : (m.factorial:ℂ)≠0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((n-m).factorial:ℂ)≠0 := by exact_mod_cast (n-m).factorial_ne_zero
  field_simp

lemma coefficient_power (m n : ℕ) (c : ℂ) :
    coefficient (fun z : ℂ => z^m) c n=(m.choose n:ℂ)*c^(m-n) := by
  unfold coefficient
  rw [iteratedDeriv_pow,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

lemma coefficient_sub (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (c : ℂ) (n : ℕ) :
    coefficient (fun z => f z-g z) c n = coefficient f c n-coefficient g c n := by
  unfold coefficient
  change iteratedDeriv n (f-g) c/(n.factorial:ℂ)=_
  rw [iteratedDeriv_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt,sub_div]

lemma coefficient_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    coefficient (fun z => a*f z) c n = a*coefficient f c n := by
  unfold coefficient
  rw [iteratedDeriv_const_mul_field]
  ring

lemma coefficient_const (a c : ℂ) (n : ℕ) :
    coefficient (fun _ : ℂ => a) c n=if n=0 then a else 0 := by
  unfold coefficient
  rw [iteratedDeriv_const]
  by_cases hn : n=0 <;> simp [hn]

lemma q_coefficient_general (n : ℕ) :
    coefficient q center n =
      (1/2:ℂ)*((2:ℕ).choose n:ℂ)*center^(2-n) -
      (1/2:ℂ)*((1:ℕ).choose n:ℂ)*center^(1-n) := by
  have he : q = fun z : ℂ => (1/2:ℂ)*z^2-(1/2:ℂ)*z^1 := by
    funext z
    unfold q
    ring
  rw [he,coefficient_sub _ _ (by fun_prop) (by fun_prop),
    coefficient_const_mul,coefficient_const_mul,coefficient_power,coefficient_power]
  ring

lemma q_coefficient_zero : coefficient q center 0=-(69697/8:ℂ) := by
  rw [q_coefficient_general]
  unfold center RH1000Analytic.CertifiedLocalXi.center
  norm_num
  ring_nf
  rw [Complex.I_sq]
  norm_num

lemma q_coefficient_one : coefficient q center 1=Complex.I*132 := by
  rw [q_coefficient_general]
  unfold center RH1000Analytic.CertifiedLocalXi.center
  norm_num
  ring

lemma q_coefficient_two : coefficient q center 2=1/2 := by
  rw [q_coefficient_general]
  norm_num

lemma q_coefficient_large (n : ℕ) (hn : 3≤n) : coefficient q center n=0 := by
  rw [q_coefficient_general]
  have h2 : (2:ℕ).choose n=0 := Nat.choose_eq_zero_of_lt (by omega)
  have h1 : (1:ℕ).choose n=0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h1,h2]

lemma q_entire : Differentiable ℂ q := by unfold q; fun_prop

lemma sum_product (n : ℕ) :
    (∑ m ∈ range (n+1), coefficient q center m * lambda (n-m)) =
      (-(69697/8:ℂ))*lambda n +
        (if 1≤n then Complex.I*(132:ℂ)*lambda (n-1) else 0) +
        (if 2≤n then (1/2:ℂ)*lambda (n-2) else 0) := by
  by_cases h0 : n=0
  · subst n
    simp [q_coefficient_zero]
  by_cases h1 : n=1
  · subst n
    norm_num [Finset.sum_range_succ,q_coefficient_zero,q_coefficient_one]
  have hn : 2≤n := by omega
  have hsub : range 3 ⊆ range (n+1) := Finset.range_mono (by omega)
  have hsum : (∑ m ∈ range (n+1), coefficient q center m*lambda (n-m)) =
      ∑ m ∈ range 3, coefficient q center m*lambda (n-m) := by
    apply (Finset.sum_subset hsub ?_).symm
    intro m hm hnot
    have hm3 : 3 ≤ m := by simpa only [mem_range,not_lt] using hnot
    rw [q_coefficient_large m hm3]
    simp
  rw [hsum]
  simp only [if_pos (by omega : 1≤n),if_pos hn]
  norm_num [Finset.sum_range_succ,q_coefficient_zero,q_coefficient_one,q_coefficient_two]

lemma xi_coefficient (n : ℕ) :
    coefficient RH1000Analytic.CertifiedLocalXi.xi center n =
      (if n=0 then (1/2:ℂ) else 0) +
      (-(69697/8:ℂ))*lambda n +
        (if 1≤n then Complex.I*(132:ℂ)*lambda (n-1) else 0) +
        (if 2≤n then (1/2:ℂ)*lambda (n-2) else 0) := by
  have hf : RH1000Analytic.CertifiedLocalXi.xi =
      fun z : ℂ => (1/2:ℂ)+q z*completedRiemannZeta₀ z := by
    funext z
    rfl
  rw [hf]
  unfold coefficient
  have hprod : Differentiable ℂ (fun z => q z*completedRiemannZeta₀ z) :=
    q_entire.mul differentiable_completedZeta₀
  rw [iteratedDeriv_fun_add (by fun_prop) hprod.contDiff.contDiffAt,add_div]
  change coefficient (fun _ : ℂ => (1/2:ℂ)) center n +
    coefficient (fun z => q z*completedRiemannZeta₀ z) center n = _
  rw [coefficient_const,coefficient_mul _ _ q_entire differentiable_completedZeta₀]
  change _ + (∑ m ∈ range (n+1), coefficient q center m*lambda (n-m)) = _
  rw [sum_product]
  ring

end DirectXi132CoefficientIdentity

open Complex
open RH1000Analytic.CertifiedTaylorQuadrature
open DirectXi132CoefficientIdentity

namespace DirectXi132Error

noncomputable def error (n : ℕ) : ℂ :=
  DirectXi132CoefficientIdentity.lambda n-RHDirect132XiCoefficients.lambda n

lemma lambda_error (n : ℕ) : ‖error n‖≤18/10^82 := by
  have h := TaoFivePrimes.rh_direct_132_completed_zeta_coefficients n
  have hc : center=((1/2:ℂ)+132*Complex.I) := by
    unfold center RH1000Analytic.CertifiedLocalXi.center
    norm_num
  change ‖coefficient completedRiemannZeta₀ center n -
    RHDirect132XiCoefficients.lambda n‖≤(18/10^82)/(2:ℝ)^n at h
  have hp : (1:ℝ)≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
  exact h.trans (div_le_self (by positivity) hp)

lemma xi_difference (n : ℕ) :
    coefficient RH1000Analytic.CertifiedLocalXi.xi center n -
        RHDirect132XiCoefficients.xi n =
      (-(69697/8:ℂ))*error n +
        (if 1≤n then Complex.I*(132:ℂ)*error (n-1) else 0) +
        (if 2≤n then (1/2:ℂ)*error (n-2) else 0) := by
  rw [xi_coefficient]
  unfold RHDirect132XiCoefficients.xi error
  by_cases h1 : 1≤n <;> by_cases h2 : 2≤n <;> simp [h1,h2] <;> ring

lemma xi_error (n : ℕ) :
    ‖coefficient RH1000Analytic.CertifiedLocalXi.xi center n -
        RHDirect132XiCoefficients.xi n‖≤2/10^77 := by
  rw [xi_difference]
  have h0 : ‖(-(69697/8:ℂ))*error n‖≤8713*(18/10^82) := by
    rw [norm_mul]
    have hh := lambda_error n
    have ha : ‖(-(69697/8:ℂ))‖≤8713 := by norm_num
    exact mul_le_mul ha hh (norm_nonneg _) (by norm_num)
  have h1 : ‖(if 1≤n then Complex.I*(132:ℂ)*error (n-1) else 0)‖≤132*(18/10^82) := by
    split_ifs with hn
    · have hh := mul_le_mul_of_nonneg_left (lambda_error (n-1))
        (show (0:ℝ)≤132 by norm_num)
      simpa [norm_mul] using hh
    · simp; positivity
  have h2 : ‖(if 2≤n then (1/2:ℂ)*error (n-2) else 0)‖≤18/10^82 := by
    split_ifs with hn
    · rw [norm_mul]
      have hh := lambda_error (n-2)
      have ha : ‖(1/2:ℂ)‖≤1 := by norm_num
      calc
        _ ≤ 1*(18/10^82) := mul_le_mul ha hh (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    · simp; positivity
  have hh := norm_add_le (-(69697/8:ℂ)*error n +
      (if 1≤n then Complex.I*(132:ℂ)*error (n-1) else 0))
      (if 2≤n then (1/2:ℂ)*error (n-2) else 0)
  have hsum := norm_add_le (-(69697/8:ℂ)*error n)
      (if 1≤n then Complex.I*(132:ℂ)*error (n-1) else 0)
  exact hh.trans ((add_le_add (hsum.trans (add_le_add h0 h1)) h2).trans (by norm_num))

end DirectXi132Error

theorem solution (n : ℕ) :
    ‖(10^43:ℂ)*Complex.I^n *
        RH1000Analytic.CertifiedTaylorQuadrature.coefficient
          RH1000Analytic.CertifiedLocalXi.xi (RH1000Analytic.CertifiedLocalXi.center 132) n -
      RHDirect132XiCoefficients.scaled n‖≤2/10^34 := by
  unfold RHDirect132XiCoefficients.scaled
  rw [←mul_sub,norm_mul]
  have h := DirectXi132Error.xi_error n
  have hh : ‖(10^43:ℂ)*Complex.I^n‖=(10^43:ℝ) := by
    simp [norm_mul,norm_pow]
  rw [hh]
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by norm_num)
