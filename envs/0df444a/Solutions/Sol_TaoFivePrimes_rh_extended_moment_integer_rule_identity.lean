-- Prove2me | solution 1 for TaoFivePrimes.rh_extended_moment_integer_rule_identity
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:05:17.592662+00:00
-- url     : https://prove2.me/submissions/fdbc3ba7-20a4-4992-baeb-9e333f29eadf

import Definitions.Def_TaoFivePrimes_RHExtendedMomentIntegerRule
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Finset

namespace RHNextMomentIntegerProof
open RHNextMomentInteger

lemma denominator_pos : 0 < weightDenominator := by
  unfold weightDenominator RH14MomentEnclosureProof.CertifiedMomentWeights.denominator
  decide

lemma denominator_divisible : ∀ j : Fin 184, j.val+1 ∣ weightDenominator := by
  unfold weightDenominator RH14MomentEnclosureProof.CertifiedMomentWeights.denominator
  decide +kernel

lemma weight_eq (j : ℕ) : RHNextMomentRule.weight j =
    if j%2=0 then 2/(j+1:ℚ) else 0 := by
  unfold RHNextMomentRule.weight
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases h : j%2=0
  · have hh : (j+1)%2=1 := by omega
    simp [hh,h]
    ring
  · have hh : (j+1)%2=0 := by omega
    simp [hh,h]

lemma weight_scaled (j : ℕ) (hj : j<184) :
    (weight j:ℚ)/(weightDenominator:ℚ)=RHNextMomentRule.weight j := by
  have hd := denominator_divisible ⟨j,hj⟩
  change (j+1) ∣ RH14MomentEnclosureProof.CertifiedMomentWeights.denominator at hd
  have hD : (weightDenominator:ℚ)≠0 := by exact_mod_cast denominator_pos.ne'
  have hj0 : ((j+1:ℕ):ℚ)≠0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [weight_eq]
  unfold weight RH14MomentEnclosureProof.CertifiedMomentWeights.weight
  by_cases h : j%2=0
  · rw [if_pos h,if_pos h,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_div hd hj0]
    push_cast
    field_simp
    rfl
  · simp [h]

lemma correlation_scaled (i m : ℕ) (hm : m<184) :
    (correlation i m:ℚ)/((CertifiedFixedPoint.scale310:ℚ)*(weightDenominator:ℚ))=
      RHNextMomentRule.correlation (RHNextMomentRule.jet i) m := by
  have hS : (CertifiedFixedPoint.scale310:ℚ)≠0 := by norm_num [CertifiedFixedPoint.scale310]
  have hD : (weightDenominator:ℚ)≠0 := by exact_mod_cast denominator_pos.ne'
  unfold correlation RHNextMomentRule.correlation
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro l hl
  have hml : m+l<184 := by have := mem_range.mp hl; omega
  rw [←weight_scaled (m+l) hml]
  unfold RHNextMomentRule.jet
  field_simp
  <;> ring

lemma fastChoose_eq (k m : ℕ) : fastChoose k m=Nat.choose k m := by
  by_cases h : m≤k
  · simp only [fastChoose,if_pos h,Nat.choose_eq_factorial_div_factorial h]
  · simp only [fastChoose,if_neg h,Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]

lemma reciprocal_factorials (k m : ℕ) (hm : m≤k) :
    (1/(m.factorial:ℚ))*(1/((k-m).factorial:ℚ))=(Nat.choose k m:ℚ)/(k.factorial:ℚ) := by
  have hc : (Nat.choose k m:ℚ)*(m.factorial:ℚ)*((k-m).factorial:ℚ)=(k.factorial:ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  have h1 : (m.factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : ((k-m).factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (k-m)
  have h3 : (k.factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp
  nlinarith only [hc]

lemma panel_term (i k m : ℕ) (hm : m≤k) (hm184 : m<184) :
    ((64:ℚ)*(3/16))^m/(m.factorial:ℚ)*
      RHNextMomentRule.correlation (RHNextMomentRule.jet i) m *
      (((64:ℚ)*RHNextMomentRule.panelCenter i)^(k-m)/((k-m).factorial:ℚ)) =
    ((correlation i m:ℚ)*(12:ℚ)^m*((12*(2*i+1):ℕ):ℚ)^(k-m)*(fastChoose k m:ℚ))/
      ((CertifiedFixedPoint.scale310:ℚ)*(weightDenominator:ℚ)*(k.factorial:ℚ)) := by
  rw [←correlation_scaled i m hm184,fastChoose_eq]
  have hc : (64:ℚ)*RHNextMomentRule.panelCenter i=(12*(2*i+1):ℕ) := by
    unfold RHNextMomentRule.panelCenter
    push_cast
    ring
  rw [hc]
  norm_num only [show (64:ℚ)*(3/16)=12 by norm_num]
  have hf := reciprocal_factorials k m hm
  have hS : (CertifiedFixedPoint.scale310:ℚ)≠0 := by norm_num [CertifiedFixedPoint.scale310]
  have hD : (weightDenominator:ℚ)≠0 := by exact_mod_cast denominator_pos.ne'
  have h1 : (m.factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : ((k-m).factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (k-m)
  have h3 : (k.factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp at hf ⊢
  rw [hf]

lemma panel_identity (i k : ℕ) :
    RHNextMomentRule.scalarPanel (RHNextMomentRule.jet i) 64
      (RHNextMomentRule.panelCenter i) (3/16) k =
    3*(panelNumerator i k:ℚ)/
      (16*(CertifiedFixedPoint.scale310:ℚ)*(weightDenominator:ℚ)*(k.factorial:ℚ)) := by
  unfold RHNextMomentRule.scalarPanel panelNumerator
  push_cast
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_div]
  apply sum_congr rfl
  intro m hm
  by_cases h : m<184
  · simp only [if_pos h]
    have hk : m≤k := by have := mem_range.mp hm; omega
    rw [panel_term i k m hk h]
    push_cast
    ring
  · simp [h]

theorem integer_rule_identity (j : ℕ) :
    TaoFivePrimes_RHExtendedMomentRule j=TaoFivePrimes_RHExtendedMomentIntegerRule j := by
  unfold TaoFivePrimes_RHExtendedMomentRule TaoFivePrimes_RHExtendedMomentIntegerRule numerator denominator
  push_cast
  simp_rw [panel_identity]
  rw [Finset.mul_sum,Finset.sum_div]

end RHNextMomentIntegerProof

theorem solution (j : ℕ) :
    TaoFivePrimes_RHExtendedMomentRule j=TaoFivePrimes_RHExtendedMomentIntegerRule j :=
  RHNextMomentIntegerProof.integer_rule_identity j
