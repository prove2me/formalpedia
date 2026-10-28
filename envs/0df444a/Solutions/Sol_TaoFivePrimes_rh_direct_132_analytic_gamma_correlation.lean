-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_analytic_gamma_correlation
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:41:01.851207+00:00
-- url     : https://prove2.me/submissions/44371a9b-3c3f-49c6-892d-2d5bc252dd51

import Definitions.Def_TaoFivePrimes_RHDirect132Rule
import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator
import Theorems.Thm_TaoFivePrimes_rh_direct_132_phase_factors
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_0
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_1
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_2
import Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_3
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
open Complex Finset
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


end RHNextMomentIntegerProof
lemma cache_correct (i m : ℕ) (hi : i<16) (hm : m<184) :
    RHNextMomentInteger.correlation i m=TaoFivePrimes_RHExtendedMomentCorrelationCache i m := by
  interval_cases i <;> first
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_0 (⟨0,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_0 (⟨1,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_0 (⟨2,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_0 (⟨3,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_1 (⟨0,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_1 (⟨1,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_1 (⟨2,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_1 (⟨3,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_2 (⟨0,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_2 (⟨1,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_2 (⟨2,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_2 (⟨3,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_3 (⟨0,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_3 (⟨1,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_3 (⟨2,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)
    | simpa [TaoFivePrimes_RHExtendedMomentCorrelationCache] using
        TaoFivePrimes.rh_extended_moment_correlations_3 (⟨3,by norm_num⟩:Fin 4) (⟨m,hm⟩:Fin 184)


namespace Direct132BaseCorrelation

lemma complex_weight (j : ℕ) :
    RHDirect132Rule.weight j = (RHNextMomentRule.weight j:ℂ) := by
  unfold RHDirect132Rule.weight RHNextMomentRule.weight
  push_cast
  rfl

lemma base_correlation (i m : ℕ) (hi : i<16) (hm : m<184) :
    (∑ r ∈ range (184-m), RHDirect132Rule.baseJet i r * RHDirect132Rule.weight (m+r)) =
      (TaoFivePrimes_RHExtendedMomentCorrelationCache i m:ℂ)/
        ((CertifiedFixedPoint.scale310:ℂ)*(RHNextMomentInteger.weightDenominator:ℂ)) := by
  have hsum :
      (∑ r ∈ range (184-m), RHDirect132Rule.baseJet i r * RHDirect132Rule.weight (m+r)) =
        (RHNextMomentRule.correlation (RHNextMomentRule.jet i) m:ℂ) := by
    unfold RHNextMomentRule.correlation
    push_cast
    apply sum_congr rfl
    intro r hr
    rw [complex_weight]
    rfl
  rw [hsum, ←cache_correct i m hi hm]
  have h := congrArg (fun x : ℚ => (x:ℂ))
    (RHNextMomentIntegerProof.correlation_scaled i m hm).symm
  push_cast at h
  exact h

end Direct132BaseCorrelation

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex Finset

namespace Direct132PhaseFactorWorking

lemma I_power_signs (l : ℕ) :
    Complex.I^l = (RHDirect132Integer.realSign l:ℂ) +
      Complex.I*(RHDirect132Integer.imagSign l:ℂ) := by
  have h : l%4=0 ∨ l%4=1 ∨ l%4=2 ∨ l%4=3 := by
    have hh := Nat.mod_lt l (by norm_num : 0<4)
    omega
  rw [Complex.I_pow_eq_pow_mod l]
  rcases h with h | h | h | h <;>
    simp only [RHDirect132Integer.realSign,RHDirect132Integer.imagSign,h] <;>
    norm_num [Complex.I_sq,Complex.I_pow_three]

lemma phase_factor_scaled (l : ℕ) (hl : l<184) :
    RHDirect132Rule.phaseJet l =
      Complex.I^l*(RHDirect132Integer.phaseFactor l:ℂ)/
        ((8:ℂ)^183*((183:ℕ).factorial:ℂ)) := by
  have hle : l≤183 := by omega
  have hdvd : l.factorial ∣ (183:ℕ).factorial := Nat.factorial_dvd_factorial hle
  have hF : (((183:ℕ).factorial/l.factorial:ℕ):ℂ)*(l.factorial:ℂ) =
      ((183:ℕ).factorial:ℂ) := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  have hf0 : (l.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  have hF0 : ((183:ℕ).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero 183
  have h8 : (8:ℂ)^l ≠ 0 := pow_ne_zero l (by norm_num)
  have h8a : (8:ℂ)^183 ≠ 0 := pow_ne_zero 183 (by norm_num)
  have hpow : (8:ℂ)^(183-l)*(8:ℂ)^l = (8:ℂ)^183 := by
    rw [←pow_add,Nat.sub_add_cancel hle]
  have hp := TaoFivePrimes.rh_direct_132_phase_factors ⟨l,hl⟩
  simp only [Fin.val_mk] at hp
  unfold RHDirect132Rule.phaseJet RHDirect132Integer.phaseFactor
  rw [hp]
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have he : Complex.I*(66:ℂ)*(3/16:ℂ) = Complex.I*((99:ℂ)/8) := by ring
  rw [he,mul_pow,div_pow]
  field_simp
  rw [←hpow]
  rw [←hF]
  ring

end Direct132PhaseFactorWorking

namespace Direct132GammaAnalytic
open Direct132PhaseFactorWorking Direct132BaseCorrelation

lemma gamma_numerator (i m : ℕ) :
    ((RHDirect132Integer.gammaRe i m:ℤ):ℂ) +
        Complex.I*((RHDirect132Integer.gammaIm i m:ℤ):ℂ) =
      ∑ l ∈ range (184-m),
        (TaoFivePrimes_RHExtendedMomentCorrelationCache i (m+l):ℂ)*
          (RHDirect132Integer.phaseFactor l:ℂ)*Complex.I^l := by
  unfold RHDirect132Integer.gammaRe RHDirect132Integer.gammaIm
  push_cast
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply sum_congr rfl
  intro l hl
  rw [I_power_signs]
  ring

lemma phase_correlation (i m : ℕ) (hi : i<16) (hm : m<184) :
    (∑ l ∈ range (184-m), RHDirect132Rule.phaseJet l *
      ∑ r ∈ range (184-m-l), RHDirect132Rule.baseJet i r * RHDirect132Rule.weight (m+l+r)) =
      (((RHDirect132Integer.gammaRe i m:ℤ):ℂ) +
        Complex.I*((RHDirect132Integer.gammaIm i m:ℤ):ℂ))/
      ((CertifiedFixedPoint.scale310:ℂ)*(RHNextMomentInteger.weightDenominator:ℂ)*
        ((8:ℂ)^183*((183:ℕ).factorial:ℂ))) := by
  rw [gamma_numerator,Finset.sum_div]
  apply sum_congr rfl
  intro l hl
  have hl' : l<184 := by have := mem_range.mp hl; omega
  have hml : m+l<184 := by have := mem_range.mp hl; omega
  rw [phase_factor_scaled l hl']
  have hb := base_correlation i (m+l) hi hml
  simp only [Nat.sub_add_eq] at hb
  rw [hb]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end Direct132GammaAnalytic

theorem solution (i m : ℕ) (hi : i<16) (hm : m<184) :
    (∑ l ∈ range (184-m), RHDirect132Rule.phaseJet l *
      ∑ r ∈ range (184-m-l), RHDirect132Rule.baseJet i r * RHDirect132Rule.weight (m+l+r)) =
      (((RHDirect132Integer.gammaRe i m:ℤ):ℂ) +
        Complex.I*((RHDirect132Integer.gammaIm i m:ℤ):ℂ))/
      ((CertifiedFixedPoint.scale310:ℂ)*(RHNextMomentInteger.weightDenominator:ℂ)*
        ((8:ℂ)^183*((183:ℕ).factorial:ℂ))) :=
  Direct132GammaAnalytic.phase_correlation i m hi hm
