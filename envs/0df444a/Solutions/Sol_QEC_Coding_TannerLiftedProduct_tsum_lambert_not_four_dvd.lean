-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tsum_lambert_not_four_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:55:39.436541+00:00
-- url     : https://prove2.me/submissions/ecdbc36d-0a08-4532-b61f-ee789dc42b72

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLaurentEvalOne_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_C_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiLaurentEvalOne_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_C_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_X
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


section
namespace QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
private theorem summable_jacobiLambertTerms_comp_ge
    (g : ℕ → ℕ) (hg : ∀ n, n ≤ g n) :
    Summable (fun n : ℕ => jacobiLambertTerm (g n)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro k
  apply summable_of_hasFiniteSupport
  refine (Finset.range (k + 1)).finite_toSet.subset ?_
  intro n hn
  simp only [Function.mem_support] at hn
  by_contra hmem
  have hnlarge : k + 1 ≤ n := by
    simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  rw [coeff_jacobiLambertTerm] at hn
  by_cases hcond : 0 < k ∧ g n ∣ k
  · have hle := Nat.le_of_dvd hcond.1 hcond.2
    have hgn := hg n
    omega
  · simp [hcond] at hn
private theorem summable_four_jacobiLambertTerms :
    Summable (fun n : ℕ => jacobiLambertTerm (4 * n)) :=
  summable_jacobiLambertTerms_comp_ge _ (by intro n; omega)
private theorem summable_notFour_jacobiLambertTerms :
    Summable (fun d : {d : ℕ // ¬4 ∣ d} => jacobiLambertTerm d.1) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro k
  apply summable_of_hasFiniteSupport
  let s : Finset {d : ℕ // ¬4 ∣ d} :=
    (Finset.Iic k).preimage Subtype.val Subtype.val_injective.injOn
  refine s.finite_toSet.subset ?_
  intro d hd
  simp only [Function.mem_support] at hd
  by_contra hmem
  have hdlarge : k < d.1 := by
    simpa [s] using hmem
  rw [coeff_jacobiLambertTerm] at hd
  by_cases hcond : 0 < k ∧ d.1 ∣ k
  · have := Nat.le_of_dvd hcond.1 hcond.2
    omega
  · simp [hcond] at hd
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option maxHeartbeats 800000
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    (∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d) =
      (∑' d : ℕ, jacobiLambertTerm d) -
        ∑' n : ℕ, jacobiLambertTerm (4 * n) := by
  have hmultiple :
      (∑' n : ℕ, jacobiLambertTerm (4 * n)) =
        ∑' d : {d : ℕ // 4 ∣ d}, jacobiLambertTerm d.1 := by
    exact fourMultipleEquiv.tsum_eq
      (fun d : {d : ℕ // 4 ∣ d} => jacobiLambertTerm d.1)
  have hmask :
      (∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d) =
        ∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1 := by
    calc
      (∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d) =
          ∑' d : ℕ, {d : ℕ | ¬4 ∣ d}.indicator jacobiLambertTerm d := by
        apply tsum_congr
        intro d
        by_cases hd : 4 ∣ d <;> simp [hd]
      _ = ∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1 :=
        (tsum_subtype {d : ℕ | ¬4 ∣ d} jacobiLambertTerm).symm
  have hpartition :
      (∑' d : {d : ℕ // 4 ∣ d}, jacobiLambertTerm d.1) +
          (∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1) =
        ∑' d : ℕ, jacobiLambertTerm d := by
    have hsc : HasSum
        (fun d : {d : ℕ // ¬4 ∣ d} => jacobiLambertTerm d.1)
        (∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1) :=
      summable_notFour_jacobiLambertTerms.hasSum
    have hwhole : HasSum jacobiLambertTerm
        ((∑' d : {d : ℕ // 4 ∣ d}, jacobiLambertTerm d.1) +
          ∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1) := by
      let g : ℕ ⊕ {d : ℕ // ¬4 ∣ d} → PowerSeries ℚ := fun d =>
        match d with
        | Sum.inl n => jacobiLambertTerm (4 * n)
        | Sum.inr d => jacobiLambertTerm d.1
      have hleft : HasSum (g ∘ Sum.inl)
          (∑' n : ℕ, jacobiLambertTerm (4 * n)) := by
        change HasSum (fun n : ℕ => jacobiLambertTerm (4 * n))
          (∑' n : ℕ, jacobiLambertTerm (4 * n))
        exact summable_four_jacobiLambertTerms.hasSum
      have hright : HasSum (g ∘ Sum.inr)
          (∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1) := by
        change HasSum
          (fun d : {d : ℕ // ¬4 ∣ d} => jacobiLambertTerm d.1)
          (∑' d : {d : ℕ // ¬4 ∣ d}, jacobiLambertTerm d.1)
        exact hsc
      apply fourPartitionEquiv.hasSum_iff.mp
      rw [← hmultiple]
      refine (hleft.sum hright).congr_fun ?_
      intro d
      rcases d with d | d
      · rfl
      · rfl
    exact hwhole.tsum_eq.symm
  rw [hmask, hmultiple]
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using hpartition
end QEC.Coding.TannerLiftedProduct
