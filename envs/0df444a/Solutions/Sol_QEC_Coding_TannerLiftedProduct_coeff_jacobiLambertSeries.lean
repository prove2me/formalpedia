-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:53:28.119195+00:00
-- url     : https://prove2.me/submissions/8a530cad-e313-432a-b653-33d62562f390

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm
section
namespace QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
private theorem summable_jacobiLambertTerms :
    Summable (fun d : ℕ => if 4 ∣ d then 0 else jacobiLambertTerm d) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro n
  apply summable_of_hasFiniteSupport
  refine (Finset.Iic n).finite_toSet.subset ?_
  intro d hd
  simp only [Function.mem_support] at hd
  by_contra hdnle
  by_cases h4 : 4 ∣ d
  · simp [h4] at hd
  · simp only [h4, if_false, coeff_jacobiLambertTerm] at hd
    by_cases hcond : 0 < n ∧ d ∣ n
    · exact hdnle (by simpa using Nat.le_of_dvd hcond.1 hcond.2)
    · simp [hcond] at hd
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n jacobiLambertSeries =
      if n = 0 then 1
      else 8 * ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d := by
  by_cases hn : n = 0
  · subst n
    rw [jacobiLambertSeries, map_add, PowerSeries.coeff_C_mul]
    rw [summable_jacobiLambertTerms.map_tsum
      (PowerSeries.coeff 0)
      (PowerSeries.WithPiTopology.continuous_coeff ℚ 0)]
    have hzero :
        (∑' i : ℕ,
          PowerSeries.constantCoeff
            (if 4 ∣ i then 0 else jacobiLambertTerm i)) = 0 := by
      have hfun :
          (fun i : ℕ => PowerSeries.constantCoeff
            (if 4 ∣ i then 0 else jacobiLambertTerm i)) = 0 := by
        funext i
        by_cases h4 : 4 ∣ i
        · simp [h4]
        · rw [if_neg h4, ← PowerSeries.coeff_zero_eq_constantCoeff]
          simp
      rw [hfun]
      change (∑' _ : ℕ, (0 : ℚ)) = 0
      exact tsum_zero
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff] using hzero
  · rw [jacobiLambertSeries, map_add, PowerSeries.coeff_C_mul]
    rw [summable_jacobiLambertTerms.map_tsum
      (PowerSeries.coeff n)
      (PowerSeries.WithPiTopology.continuous_coeff ℚ n)]
    rw [tsum_eq_sum (s := n.divisors)]
    · rw [PowerSeries.coeff_one]
      simp only [hn, if_false, zero_add]
      push_cast
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      by_cases h4 : 4 ∣ d <;> simp [h4, hnpos, hdvd]
    · intro d hd
      have hnotdvd : ¬ d ∣ n := by
        intro hdvd
        exact hd (Nat.mem_divisors.mpr ⟨hdvd, hn⟩)
      by_cases h4 : 4 ∣ d <;> simp [h4, hnotdvd]
end QEC.Coding.TannerLiftedProduct
