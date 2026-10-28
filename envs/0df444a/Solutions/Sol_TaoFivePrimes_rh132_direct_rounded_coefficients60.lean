-- Prove2me | solution 1 for TaoFivePrimes.rh132_direct_rounded_coefficients60
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:58:27.840991+00:00
-- url     : https://prove2.me/submissions/f39d4e54-d75a-46e6-9113-afbcdac94656

import Theorems.Thm_TaoFivePrimes_rh_direct_132_cached_rule_identity60
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_all
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_component_error
import Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_all
import Definitions.Def_TaoFivePrimes_RH132RoundingSpec
import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib
set_option autoImplicit false
open Complex Finset
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex

namespace Direct132LambdaFixed

lemma sign_of_parity (n : ℕ) :
    (-1:ℂ)^n = if n%2=0 then 1 else -1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  have h : n%2=0 ∨ n%2=1 := by have hh := Nat.mod_lt n (by norm_num : 0<2); omega
  rcases h with h | h <;> simp [h]

lemma folded_real (n : ℕ) (R : ℂ) (hn : n%2=0) :
    (R+(-1:ℂ)^n*star R)/(2:ℂ)^(n+1) = (R.re:ℂ)/(2:ℂ)^n := by
  rw [sign_of_parity,if_pos hn,one_mul]
  have hnum : R+star R=(2:ℂ)*(R.re:ℂ) := by
    apply Complex.ext <;> simp [Complex.star_def,Complex.mul_re,Complex.mul_im] <;> ring
  rw [hnum,pow_succ]
  have hpow : (2:ℂ)^n≠0 := pow_ne_zero n (by norm_num)
  field_simp

lemma folded_imag (n : ℕ) (R : ℂ) (hn : n%2≠0) :
    (R+(-1:ℂ)^n*star R)/(2:ℂ)^(n+1) = Complex.I*(R.im:ℂ)/(2:ℂ)^n := by
  rw [sign_of_parity,if_neg hn,neg_one_mul,←sub_eq_add_neg]
  have hnum : R-star R=Complex.I*(2:ℂ)*(R.im:ℂ) := by
    apply Complex.ext <;> simp [Complex.star_def,Complex.mul_re,Complex.mul_im] <;> ring
  rw [hnum,pow_succ]
  have hpow : (2:ℂ)^n≠0 := pow_ne_zero n (by norm_num)
  field_simp

lemma approximation (n : ℕ) (R : ℂ) (q : ℝ)
    (h : |(if n%2=0 then R.re else R.im)-q| ≤ 1/10^90) :
    ‖(R+(-1:ℂ)^n*star R)/(2:ℂ)^(n+1) -
      (if n%2=0 then ((q/(2:ℝ)^n:ℝ):ℂ)
       else Complex.I*((q/(2:ℝ)^n:ℝ):ℂ))‖ ≤ 1/10^90 := by
  have hp : (1:ℝ)≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hp0 : 0≤(2:ℝ)^n := by positivity
  by_cases hn : n%2=0
  · simp only [hn,if_true] at h ⊢
    rw [folded_real n R hn]
    have he : (R.re:ℂ)/(2:ℂ)^n-((q/(2:ℝ)^n:ℝ):ℂ) =
        (((R.re-q)/(2:ℝ)^n:ℝ):ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_nonneg hp0]
    exact (div_le_self (abs_nonneg _) hp).trans h
  · simp only [hn,if_false] at h ⊢
    rw [folded_imag n R hn]
    have he : Complex.I*(R.im:ℂ)/(2:ℂ)^n-Complex.I*((q/(2:ℝ)^n:ℝ):ℂ) =
        Complex.I*(((R.im-q)/(2:ℝ)^n:ℝ):ℂ) := by push_cast; ring
    rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_div,abs_of_nonneg hp0]
    exact (div_le_self (abs_nonneg _) hp).trans h

end Direct132LambdaFixed

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex

namespace Direct132XiFixedError

lemma coefficient_error (n : ℕ)
    (h0 : ‖RHDirect132XiCoefficients.lambda n-RHDirect132FixedXi.lambdaC n‖≤1/10^90)
    (h1 : 1≤n → ‖RHDirect132XiCoefficients.lambda (n-1)-RHDirect132FixedXi.lambdaC (n-1)‖≤1/10^90)
    (h2 : 2≤n → ‖RHDirect132XiCoefficients.lambda (n-2)-RHDirect132FixedXi.lambdaC (n-2)‖≤1/10^90) :
    ‖RHDirect132XiCoefficients.scaled n-RHDirect132FixedXi.xiC n‖≤1/10^43 := by
  let d : ℕ → ℂ := fun j => RHDirect132XiCoefficients.lambda j-RHDirect132FixedXi.lambdaC j
  have hid : RHDirect132XiCoefficients.scaled n-RHDirect132FixedXi.xiC n =
      (10^43:ℂ)*Complex.I^n *
        ((-(69697/8:ℂ))*d n +
          (if 1≤n then Complex.I*(132:ℂ)*d (n-1) else 0) +
          (if 2≤n then (1/2:ℂ)*d (n-2) else 0)) := by
    unfold RHDirect132XiCoefficients.scaled RHDirect132XiCoefficients.xi RHDirect132FixedXi.xiC d
    split_ifs <;> ring
  have hb0 : ‖(-(69697/8:ℂ))*d n‖≤(69697/8:ℝ)*(1/10^90) := by
    calc
      _ = (69697/8:ℝ)*‖d n‖ := by norm_num [norm_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h0 (by norm_num)
  have hb1 : ‖if 1≤n then Complex.I*(132:ℂ)*d (n-1) else 0‖≤(132:ℝ)*(1/10^90) := by
    by_cases hn : 1≤n
    · simp only [if_pos hn,norm_mul,Complex.norm_I,one_mul]
      norm_num only [Complex.norm_ofNat]
      have hh : ‖d (n-1)‖≤(1/10^90:ℝ) := h1 hn
      nlinarith only [hh]
    · simp [hn]
  have hb2 : ‖if 2≤n then (1/2:ℂ)*d (n-2) else 0‖≤(1/2:ℝ)*(1/10^90) := by
    by_cases hn : 2≤n
    · simp only [if_pos hn,norm_mul]
      norm_num only [norm_div,norm_one,Complex.norm_ofNat]
      have hh : ‖d (n-2)‖≤(1/10^90:ℝ) := h2 hn
      nlinarith only [hh]
    · simp [hn]
  have hs :
      ‖(-(69697/8:ℂ))*d n + (if 1≤n then Complex.I*(132:ℂ)*d (n-1) else 0) +
        (if 2≤n then (1/2:ℂ)*d (n-2) else 0)‖ ≤
          ((69697/8:ℝ)+132+1/2)*(1/10^90) := by
    have h := norm_add_le ((-(69697/8:ℂ))*d n +
      (if 1≤n then Complex.I*(132:ℂ)*d (n-1) else 0))
      (if 2≤n then (1/2:ℂ)*d (n-2) else 0)
    have hh := norm_add_le ((-(69697/8:ℂ))*d n)
      (if 1≤n then Complex.I*(132:ℂ)*d (n-1) else 0)
    linarith
  rw [hid,norm_mul]
  have hn : ‖(10^43:ℂ)*Complex.I^n‖=(10^43:ℝ) := by
    simp [norm_mul,norm_pow]
  rw [hn]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans (by norm_num)

end Direct132XiFixedError

namespace Direct132RoundedFinal

lemma lambda_error (n : ℕ) (hn : n<60) :
    ‖RHDirect132XiCoefficients.lambda n-RHDirect132FixedXi.lambdaC n‖ ≤ 1/10^90 := by
  have hf := TaoFivePrimes.rh_direct_132_fixed_floor_all n hn
  have hc := TaoFivePrimes.rh_direct_132_fixed_component_error n hf
  have hr := TaoFivePrimes.rh_direct_132_cached_rule_identity60 n hn
  have hq : (RHDirect132FixedXi.lambdaQ n:ℂ) =
      (((((RHDirect132FastNumerator.fixed n:ℝ)/10^90)/(2:ℝ)^n):ℝ):ℂ) := by
    unfold RHDirect132FixedXi.lambdaQ
    push_cast
    ring
  have h := Direct132LambdaFixed.approximation n (RHDirect132CachedRule.value n)
    ((RHDirect132FastNumerator.fixed n:ℝ)/10^90) hc
  unfold RHDirect132XiCoefficients.lambda RHDirect132FixedXi.lambdaC
  rw [hr,hq]
  exact h

lemma target_cast (n : ℕ) : (RHDirect132FixedXi.targetQ n:ℝ) = RH132RoundingSpec.proposed n := by
  unfold RHDirect132FixedXi.targetQ RH132RoundingSpec.proposed
  push_cast
  rfl

lemma bound_cast (n : ℕ) : (RHDirect132FixedXi.boundQ n:ℝ) = RH132RoundingSpec.bound n := by
  unfold RHDirect132FixedXi.boundQ RH132RoundingSpec.bound
  split_ifs <;> norm_num

end Direct132RoundedFinal

theorem solution (n : ℕ) (hn : n<60) :
    ‖RHDirect132XiCoefficients.scaled n-(RH132RoundingSpec.proposed n:ℂ)‖ ≤
      RH132RoundingSpec.bound n := by
  have h0 := Direct132RoundedFinal.lambda_error n hn
  have h1 : 1≤n → ‖RHDirect132XiCoefficients.lambda (n-1)-
      RHDirect132FixedXi.lambdaC (n-1)‖≤1/10^90 := by
    intro h
    exact Direct132RoundedFinal.lambda_error (n-1) (by omega)
  have h2 : 2≤n → ‖RHDirect132XiCoefficients.lambda (n-2)-
      RHDirect132FixedXi.lambdaC (n-2)‖≤1/10^90 := by
    intro h
    exact Direct132RoundedFinal.lambda_error (n-2) (by omega)
  have herr := Direct132XiFixedError.coefficient_error n h0 h1 h2
  have hxi := TaoFivePrimes.rh_direct_132_fixed_xi_all n hn
  have hrat : |(RHDirect132FixedXi.xiQ n:ℝ)-(RHDirect132FixedXi.targetQ n:ℝ)|+
      1/10^43 ≤ (RHDirect132FixedXi.boundQ n:ℝ) := by
    unfold RHDirect132FixedXi.roundingHolds at hxi
    have hc : ((|RHDirect132FixedXi.xiQ n-RHDirect132FixedXi.targetQ n|+
        1/10^43:ℚ):ℝ) ≤ (RHDirect132FixedXi.boundQ n:ℝ) := by
      exact Rat.cast_le.mpr hxi.2
    push_cast at hc
    exact hc
  rw [Direct132RoundedFinal.target_cast,Direct132RoundedFinal.bound_cast] at hrat
  have hnum : ‖RHDirect132FixedXi.xiC n-(RH132RoundingSpec.proposed n:ℂ)‖ =
      |(RHDirect132FixedXi.xiQ n:ℝ)-RH132RoundingSpec.proposed n| := by
    rw [hxi.1]
    have hcast : (RHDirect132FixedXi.xiQ n:ℂ)=((RHDirect132FixedXi.xiQ n:ℝ):ℂ) := by norm_cast
    rw [hcast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have hid : RHDirect132XiCoefficients.scaled n-(RH132RoundingSpec.proposed n:ℂ) =
      (RHDirect132XiCoefficients.scaled n-RHDirect132FixedXi.xiC n) +
        (RHDirect132FixedXi.xiC n-(RH132RoundingSpec.proposed n:ℂ)) := by ring
  rw [hid]
  calc
    _ ≤ ‖RHDirect132XiCoefficients.scaled n-RHDirect132FixedXi.xiC n‖ +
        ‖RHDirect132FixedXi.xiC n-(RH132RoundingSpec.proposed n:ℂ)‖ := norm_add_le _ _
    _ ≤ 1/10^43+|(RHDirect132FixedXi.xiQ n:ℝ)-RH132RoundingSpec.proposed n| := by
      rw [hnum]
      exact add_le_add herr le_rfl
    _ ≤ RH132RoundingSpec.bound n := by linarith
