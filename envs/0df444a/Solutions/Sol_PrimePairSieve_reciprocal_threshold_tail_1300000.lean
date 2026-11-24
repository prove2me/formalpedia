-- Prove2me | solution 1 for PrimePairSieve.reciprocal_threshold_tail_1300000
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:22:53.389074+00:00
-- url     : https://prove2.me/submissions/2cfd6ea7-01c9-477e-8209-ab977fcb3743

import Mathlib
import Theorems.Thm_PrimePairSieve_prime_second_logarithmic_moment_upper_bound
import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_quadratic_expansion_explicit_certified
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate

open scoped BigOperators
open Set
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section

namespace ReciprocalThresholdTail1300000

private lemma log_lower (z : ℝ) (hz : 1300000 ≤ z) : 14 ≤ Real.log z := by
  have h : Real.log (1250000:ℝ) ≤ Real.log z :=
    Real.strictMonoOn_log.monotoneOn (by norm_num)
      (show z ∈ Ioi 0 by change 0<z; linarith) (by linarith)
  have heq : Real.log (1250000:ℝ) = 4*Real.log 2+7*Real.log 5 := by
    rw [show (1250000:ℝ)=2^4*5^7 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [heq] at h
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

private lemma log_endpoint_upper : Real.log (5200000:ℝ) ≤ 16 := by
  have h : Real.log (5200000:ℝ) ≤ Real.log ((2:ℝ)^23) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_lt_d9]

private def logFourthRatio (x : ℝ) := Real.log (4*x)^4/x

private lemma ratio_deriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt logFourthRatio (Real.log (4*x)^3*(4-Real.log (4*x))/x^2) x := by
  have hlog := ((hasDerivAt_id' x).const_mul 4).log (by positivity : 4*x≠0)
  have h := (hlog.pow 4).div (hasDerivAt_id' x) hx.ne'
  convert! h using 1 <;> (try simp [logFourthRatio]) <;> field_simp [hx.ne'] <;> ring

private lemma ratio_antitone : AntitoneOn logFourthRatio (Ici 1300000) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1300000)
    (fun x hx => (ratio_deriv x (by change 1300000≤x at hx; linarith)).continuousAt.continuousWithinAt)
    (fun x hx => (ratio_deriv x (by
      have h : 1300000<x := by simpa using hx
      linarith)).hasDerivWithinAt)
  intro x hx
  have hx0 : 0<x := by
    have h : 1300000<x := by simpa using hx
    linarith
  have hx4 : 1300000≤4*x := by
    have h : 1300000<x := by simpa using hx
    linarith
  have hl := log_lower (4*x) hx4
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (sq_nonneg x)

private lemma logarithmic_tail (z : ℝ) (hz : 1300000 ≤ z) :
    Real.log (4*z)^4/z ≤ (16^4/1300000:ℝ) := by
  have h := ratio_antitone (by norm_num : (1300000:ℝ)∈Ici 1300000) hz hz
  have hlog0 : 0 ≤ Real.log (5200000:ℝ) := by positivity
  have hs := pow_le_pow_left₀ hlog0 log_endpoint_upper 4
  unfold logFourthRatio at h
  norm_num only at h
  nlinarith

private lemma power_tail (z : ℝ) (hz : 1300000 ≤ z) : z^(-(1/3:ℝ)) ≤ 1/109 := by
  have hz0 : 0<z := by linarith
  have hroot : (109:ℝ) ≤ z^(1/3:ℝ) := by
    have h := (Real.le_rpow_inv_iff_of_pos (by norm_num : (0:ℝ)≤109) hz0.le
      (by norm_num : (0:ℝ)<3)).mpr (by norm_num; linarith)
    simpa using h
  rw [Real.rpow_neg hz0.le]
  simpa only [one_div] using (inv_le_inv₀ (Real.rpow_pos_of_pos hz0 _) (by norm_num : (0:ℝ)<109)).mpr hroot

private lemma compare (C γ P B E S z : ℝ)
    (hC : 1.25 ≤ C) (hC' : C ≤ 1.3217) (hγ : 0.5722 ≤ γ) (hP : 0.74 ≤ P)
    (hB : -(47/20) ≤ B) (hE : 0 ≤ E) (hE' : E ≤ 127185/154) (hz : 1300000 ≤ z)
    (hS : (Real.log z^2+(4*γ+4*P-Real.log 2)*Real.log z+B)/(2*C)-
      E*z^(-(1/3:ℝ)) ≤ S) :
    (Real.log (4*z)^2/(2*C))/(1-(z+1)*(Real.log (4*z)^2/(2*C))/(16*z^2)) ≤ S := by
  let q := Real.log (4*z)^2/(2*C)
  let g := (z+1)/(16*z^2)
  have hz0 : 0<z := by linarith
  have hC0 : 0<2*C := by linarith
  have hl := log_lower z hz
  have hl4 := log_lower (4*z) (by linarith)
  have hp4 := logarithmic_tail z hz
  have hq0 : 0≤q := by dsimp [q]; positivity
  have hg0 : 0≤g := by dsimp [g]; positivity
  have hg : g ≤ 1/(8*z) := by
    dsimp [g]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hq : q ≤ (2/5)*Real.log (4*z)^2 := by
    dsimp [q]
    apply (div_le_iff₀ hC0).mpr
    nlinarith [mul_nonneg (sq_nonneg (Real.log (4*z))) (show 0≤C-1.25 by linarith)]
  have hlogpowers : Real.log (4*z)^2 ≤ Real.log (4*z)^4 := by
    nlinarith [sq_nonneg (Real.log (4*z)^2-1)]
  have hprod : g*q ≤ (16^4/26000000:ℝ) := by
    calc
      _ ≤ (1/(8*z))*((2/5)*Real.log (4*z)^2) :=
        mul_le_mul hg hq hq0 (by positivity)
      _ = Real.log (4*z)^2/z/20 := by ring
      _ ≤ Real.log (4*z)^4/z/20 := by gcongr
      _ ≤ (16^4/1300000)/20 := by gcongr
      _ = _ := by norm_num
  have hden : 0<1-g*q := by norm_num at hprod; linarith
  have hcorr : q/(1-g*q) ≤ q+(16^4/32500000:ℝ) := by
    have h1 : q/(1-g*q) ≤ q+2*g*q^2 := by
      apply (div_le_iff₀ hden).mpr
      have hmul := mul_nonneg (mul_nonneg hg0 (sq_nonneg q))
        (show 0≤1-2*g*q by norm_num at hprod; linarith)
      nlinarith
    have h2 : 2*g*q^2 ≤ (16^4/32500000:ℝ) := by
      calc
        _ ≤ 2*(1/(8*z))*(((2/5)*Real.log (4*z)^2)^2) := by gcongr
        _ = Real.log (4*z)^4/z/25 := by ring
        _ ≤ (16^4/1300000)/25 := by gcongr
        _ = _ := by norm_num
    linarith
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2up : Real.log 2 ≤ (0.7:ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog2sq := pow_le_pow_left₀ hlog2 hlog2up 2
  have hcoeff : (1.7488:ℝ) ≤ 4*γ+4*P-5*Real.log 2 := by linarith
  have hdelta : (20.1732:ℝ) ≤
      (4*γ+4*P-5*Real.log 2)*Real.log z+B-4*Real.log 2^2 := by
    have hmul := mul_le_mul hcoeff hl (by norm_num : (0:ℝ)≤14)
      (by linarith : 0≤4*γ+4*P-5*Real.log 2)
    nlinarith
  have hquot : (20.1732/2.6434:ℝ) ≤
      ((4*γ+4*P-5*Real.log 2)*Real.log z+B-4*Real.log 2^2)/(2*C) := by
    apply (le_div_iff₀ hC0).mpr
    nlinarith
  have hErr : E*z^(-(1/3:ℝ)) ≤ (127185/16786:ℝ) := by
    have h := mul_le_mul hE' (power_tail z hz) (by positivity) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlogeq : Real.log (4*z)=2*Real.log 2+Real.log z := by
    rw [Real.log_mul (by norm_num) hz0.ne', show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    norm_num
  have hcenter : (Real.log z^2+(4*γ+4*P-Real.log 2)*Real.log z+B)/(2*C) =
      q+((4*γ+4*P-5*Real.log 2)*Real.log z+B-4*Real.log 2^2)/(2*C) := by
    dsimp [q]
    rw [hlogeq]
    ring
  rw [hcenter] at hS
  have htarget : (Real.log (4*z)^2/(2*C))/(1-(z+1)*(Real.log (4*z)^2/(2*C))/(16*z^2)) =
      q/(1-g*q) := by dsimp [q,g]; ring
  rw [htarget]
  linarith

private lemma lower_constant (γ P Q : ℝ) (hγ : 0.5722 ≤ γ) (hP : 0.74 ≤ P) (hQ : Q ≤ 8) :
    -(47/20) ≤ 2*γ^2+4*γ*(2*P+Real.log 2/2)+
      ((2*P+Real.log 2/2)^2+(1/4:ℝ)*Real.log 2^2-Q)-
        (4*γ+4*P+Real.log 2)*Real.log 2+Real.pi^2/6 := by
  have hl0 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hl : Real.log 2 ≤ (0.7:ℝ) := by linarith [Real.log_two_lt_d9]
  have hl2 := pow_le_pow_left₀ hl0 hl 2
  have hg2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤0.5722) hγ 2
  have hglog := mul_le_mul_of_nonneg_left hl (show 0≤2*γ by linarith)
  have hplog := mul_le_mul_of_nonneg_left hl (show 0≤2*P by linarith)
  have hprod := mul_le_mul (show (4.52:ℝ)≤8*P-1.4 by linarith) hγ
    (by norm_num : (0:ℝ)≤0.5722) (show 0≤8*P-1.4 by linarith)
  have hpoly := mul_nonneg (show 0≤P-0.74 by linarith) (show 0≤4*P+1.56 by linarith)
  have hpi2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) Real.pi_gt_three.le 2
  nlinarith

end ReciprocalThresholdTail1300000
end

theorem solution :
    ∀ z : ℝ, 1300000 ≤ z →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by
  rcases PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_explicit_certified with
    ⟨B,E,hE,hEmax,hB,hbound⟩
  rcases PrimePairSieve.sieve_constants_certificate with ⟨hC,hCmax,hγ,hP⟩
  let P : ℝ := ∑' p : Nat.Primes, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))
  let Q : ℝ := ∑' p : Nat.Primes,
    (8*(p:ℝ)^2-10*(p:ℝ)+4)/((p:ℝ)^2*((p:ℝ)-1)^2)*Real.log (p:ℝ)^2
  have hQ : Q ≤ 8 := PrimePairSieve.prime_second_logarithmic_moment_upper_bound
  have hB' : -(47/20) ≤ B := (ReciprocalThresholdTail1300000.lower_constant
    Real.eulerMascheroniConstant P Q hγ hP hQ).trans hB
  intro z hz
  have hz0 : 0<z := by linarith
  have hS := (abs_le.mp (hbound z hz0)).1
  apply ReciprocalThresholdTail1300000.compare TaoFivePrimes.twinPrimeConstant
    Real.eulerMascheroniConstant P B E _ z hC hCmax hγ hP hB' hE hEmax hz
  linarith

#print axioms solution
