-- Prove2me | solution 1 for OddGoldbach19.reciprocal_denominator_five_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T17:09:33.949697+00:00
-- url     : https://prove2.me/submissions/72d1bd00-8e04-4ab2-b666-b8d75e1086c1

/- The lower-constant calculation is adapted from public Prove2Me submission
8679101a-e42f-483f-8760-f50560699bbe (Apache 2.0). The refined cutoff-five
denominator comparisons below are new consequences, kept private. -/
import Mathlib
import Theorems.Thm_PrimePairSieve_prime_second_logarithmic_moment_upper_bound
import Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_quadratic_expansion_explicit_certified
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace RefinedDenominator
noncomputable def S (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
    (if Squarefree n then
      ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ)-2)
     else 0) / (1+(n : ℝ)/z)
private lemma lower_constant (γ P Q : ℝ) (hγ : 0.5722 ≤ γ) (hP : 0.74 ≤ P) (hQ : Q ≤ 8) :
    -3 ≤ 2*γ^2+4*γ*(2*P+Real.log 2/2)+
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

private lemma power_tail (z t : ℝ) (hz : 0 < z) (ht : 0 < t)
    (hl : Real.log t ≤ Real.log z / 3) : z^(-(1/3:ℝ)) ≤ 1/t := by
  calc
    _ ≤ Real.exp (-Real.log t) := by
      rw [Real.rpow_def_of_pos hz]
      apply Real.exp_le_exp.mpr
      linarith
    _ = 1/t := by rw [Real.exp_neg, Real.exp_log ht]; simp [one_div]

private lemma lower (z t : ℝ) (hz : 0 < z) (ht : 0 < t)
    (hu : 0 ≤ Real.log z) (hl : Real.log t ≤ Real.log z/3) :
    (Real.log z^2+4.55*Real.log z-3)/(2*TaoFivePrimes.twinPrimeConstant)-826/t ≤ S z := by
  rcases PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_explicit_certified with
    ⟨B,E,hE,hEmax,hB,hbound⟩
  rcases PrimePairSieve.sieve_constants_certificate with ⟨hC,hCmax,hγ,hP⟩
  let P : ℝ := ∑' p : Nat.Primes, Real.log (p:ℝ)/((p:ℝ)*((p:ℝ)-1))
  let Q : ℝ := ∑' p : Nat.Primes,
    (8*(p:ℝ)^2-10*(p:ℝ)+4)/((p:ℝ)^2*((p:ℝ)-1)^2)*Real.log (p:ℝ)^2
  have hQ : Q ≤ 8 := PrimePairSieve.prime_second_logarithmic_moment_upper_bound
  have hB' : -3 ≤ B := (lower_constant Real.eulerMascheroniConstant P Q hγ hP hQ).trans hB
  have hcoeff : (4.55:ℝ) ≤ 4*Real.eulerMascheroniConstant+4*P-Real.log 2 := by
    dsimp [P] at *
    linarith [Real.log_two_lt_d9]
  have hcen : (Real.log z^2+4.55*Real.log z-3)/(2*TaoFivePrimes.twinPrimeConstant) ≤
      (Real.log z^2+(4*Real.eulerMascheroniConstant+4*P-Real.log 2)*Real.log z+B)/
        (2*TaoFivePrimes.twinPrimeConstant) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) hu]
  have herr : E*z^(-(1/3:ℝ)) ≤ 826/t := by
    have hh := mul_le_mul (show E ≤ 826 by linarith) (power_tail z t hz ht hl)
      (by positivity) (by norm_num : (0:ℝ) ≤ 826)
    simpa only [mul_one_div] using hh
  have h := (abs_le.mp (hbound z hz)).1
  change -(E*z^(-(1/3:ℝ))) ≤ S z - _ at h
  linarith

private lemma scaled (z t b : ℝ) (hz : 0 < z) (ht : 0 < t)
    (hu : 0 ≤ Real.log z) (hl : Real.log t ≤ Real.log z/3)
    (hb : 3+2*1.3217*826/t ≤ b) :
    4*(Real.log z^2+4.55*Real.log z-b) ≤
      8*TaoFivePrimes.twinPrimeConstant*S z := by
  have h := lower z t hz ht hu hl
  rcases PrimePairSieve.sieve_constants_certificate with ⟨hC,hCmax,-,-⟩
  have hmul := mul_le_mul_of_nonneg_left h (show 0≤2*TaoFivePrimes.twinPrimeConstant by linarith)
  rw [mul_sub, mul_div_cancel₀ _ (by linarith)] at hmul
  have hErr : (826/t)*(2*TaoFivePrimes.twinPrimeConstant) ≤ b-3 := by
    have hh := mul_le_mul_of_nonneg_left hCmax (show 0 ≤ 2*826/t by positivity)
    calc
      _ = (2*826/t)*TaoFivePrimes.twinPrimeConstant := by ring
      _ ≤ (2*826/t)*1.3217 := hh
      _ = 2*1.3217*826/t := by ring
      _ ≤ b-3 := by linarith
  nlinarith

private lemma cutoff_logs (x : ℝ) (hx : 0 < x) :
    0 < Real.sqrt x / Real.sqrt 5 ∧
    Real.log (Real.sqrt x / Real.sqrt 5) = Real.log x/2-Real.log 5/2 := by
  constructor
  · positivity
  · rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hx.le,
      Real.log_sqrt (by norm_num : (0:ℝ)≤5)]

end RefinedDenominator

theorem OddGoldbach19.reciprocal_denominator_five (x : ℝ) (hx : 0 < x)
    (hl : 40 ≤ Real.log x) :
    Real.log x*(Real.log x+4.5) ≤
      8*TaoFivePrimes.twinPrimeConstant*
        RefinedDenominator.S (Real.sqrt x/Real.sqrt 5) := by
  obtain ⟨hz,hlog⟩ := RefinedDenominator.cutoff_logs x hx
  have h5 : Real.log 5 ≤ (1.61:ℝ) := by linarith [Real.log_five_lt_d9]
  have hu : 19 ≤ Real.log (Real.sqrt x/Real.sqrt 5) := by rw [hlog]; linarith
  have ht : Real.log (500:ℝ) ≤ Real.log (Real.sqrt x/Real.sqrt 5)/3 := by
    have he : Real.log (500:ℝ) = 2*Real.log 2+3*Real.log 5 := by
      rw [show (500:ℝ)=2^2*5^3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow, Real.log_pow]; norm_num
    rw [he]; linarith [Real.log_two_lt_d9]
  have hs := RefinedDenominator.scaled (Real.sqrt x/Real.sqrt 5) 500 8 hz (by norm_num)
    (by linarith) ht (by norm_num)
  have huv : Real.log x/2-0.805 ≤ Real.log (Real.sqrt x/Real.sqrt 5) := by rw [hlog]; linarith
  have hv : 0 ≤ Real.log x/2-0.805 := by linarith
  have hsq := pow_le_pow_left₀ hv huv 2
  nlinarith

theorem OddGoldbach19.reciprocal_denominator_five_large (x : ℝ) (hx : 0 < x)
    (hl : 100 ≤ Real.log x) :
    Real.log x*(Real.log x+5.6) ≤
      8*TaoFivePrimes.twinPrimeConstant*
        RefinedDenominator.S (Real.sqrt x/Real.sqrt 5) := by
  obtain ⟨hz,hlog⟩ := RefinedDenominator.cutoff_logs x hx
  have h5 : Real.log 5 ≤ (1.61:ℝ) := by linarith [Real.log_five_lt_d9]
  have hu : 49 ≤ Real.log (Real.sqrt x/Real.sqrt 5) := by rw [hlog]; linarith
  have ht : Real.log (1000000:ℝ) ≤ Real.log (Real.sqrt x/Real.sqrt 5)/3 := by
    have he : Real.log (1000000:ℝ) = 6*(Real.log 2+Real.log 5) := by
      rw [show (1000000:ℝ)=(2*5)^6 by norm_num, Real.log_pow,
        Real.log_mul (by norm_num) (by norm_num)] <;> norm_num
    rw [he]; linarith [Real.log_two_lt_d9]
  have hs := RefinedDenominator.scaled (Real.sqrt x/Real.sqrt 5) 1000000 3.01 hz (by norm_num)
    (by linarith) ht (by norm_num)
  have huv : Real.log x/2-0.805 ≤ Real.log (Real.sqrt x/Real.sqrt 5) := by rw [hlog]; linarith
  have hv : 0 ≤ Real.log x/2-0.805 := by linarith
  have hsq := pow_le_pow_left₀ hv huv 2
  nlinarith

#print axioms OddGoldbach19.reciprocal_denominator_five_large

theorem solution (x : ℝ) (hx : 0<x)
    (hl : 40 ≤ Real.log x) :
    Real.log x*(Real.log x+4.5) ≤ 8*TaoFivePrimes.twinPrimeConstant*(∑ n ∈ Finset.Icc 1 ⌊(Real.sqrt x/Real.sqrt 5)⌋₊,
    (if Squarefree n then ∏ p ∈ n.primeFactors,
      if p=2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/(Real.sqrt x/Real.sqrt 5))) ∧
      (100 ≤ Real.log x → Real.log x*(Real.log x+5.6) ≤ 8*TaoFivePrimes.twinPrimeConstant*(∑ n ∈ Finset.Icc 1 ⌊(Real.sqrt x/Real.sqrt 5)⌋₊,
    (if Squarefree n then ∏ p ∈ n.primeFactors,
      if p=2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/(Real.sqrt x/Real.sqrt 5)))) := by
  constructor
  · exact OddGoldbach19.reciprocal_denominator_five x hx hl
  · exact OddGoldbach19.reciprocal_denominator_five_large x hx
