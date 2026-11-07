-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeries_finiteFraction_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:33:47.510196+00:00
-- url     : https://prove2.me/submissions/061b4aca-1559-49ec-adba-9d489df4133b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_mul_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRetraction_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_C_mul_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (A U : PowerSeries ℚ) (T : ι → PowerSeries ℚ) (a b : ι → ℂ)
    (h : PowerSeries.map (algebraMap ℚ ℂ) A *
          (∑ i, PowerSeries.C (a i) * PowerSeries.map (algebraMap ℚ ℂ) (T i)) =
        PowerSeries.map (algebraMap ℚ ℂ) U *
          (∑ i, PowerSeries.C (b i) * PowerSeries.map (algebraMap ℚ ℂ) (T i)))
    (hS : (∑ i, PowerSeries.C (b i) *
      PowerSeries.map (algebraMap ℚ ℂ) (T i)) ≠ 0) :
    ∃ aq bq : ι → ℚ,
      A * (∑ i, PowerSeries.C (aq i) * T i) =
        U * (∑ i, PowerSeries.C (bq i) * T i) ∧
      (∑ i, PowerSeries.C (bq i) * T i) ≠ 0 := by
  classical
  let R : PowerSeries ℂ := ∑ i, PowerSeries.C (a i) *
    PowerSeries.map (algebraMap ℚ ℂ) (T i)
  let S : PowerSeries ℂ := ∑ i, PowerSeries.C (b i) *
    PowerSeries.map (algebraMap ℚ ℂ) (T i)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, S.coeff n ≠ 0 := by
    by_contra! hh
    apply hS
    change S = 0
    ext n
    simpa only [map_zero] using hh n
  let c : ℂ := (S.coeff n)⁻¹
  let aq : ι → ℚ := fun i => lpsOriginalRationalRetraction (c * a i)
  let bq : ι → ℚ := fun i => lpsOriginalRationalRetraction (c * b i)
  have transfer (v : ι → ℂ) :
      lpsOriginalRationalSeriesRetraction
          (PowerSeries.C c *
            (∑ i, PowerSeries.C (v i) *
              PowerSeries.map (algebraMap ℚ ℂ) (T i))) =
        ∑ i, PowerSeries.C (lpsOriginalRationalRetraction (c * v i)) * T i := by
    rw [Finset.mul_sum, lpsOriginalRationalSeriesRetraction_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← mul_assoc, ← map_mul, lpsOriginalRationalSeriesRetraction_C_mul_map]
  have hscaled :
      (PowerSeries.C c * R) * PowerSeries.map (algebraMap ℚ ℂ) A =
        (PowerSeries.C c * S) * PowerSeries.map (algebraMap ℚ ℂ) U := by
    have hc := congrArg (fun V : PowerSeries ℂ => PowerSeries.C c * V) h
    change PowerSeries.C c *
        (PowerSeries.map (algebraMap ℚ ℂ) A * R) =
      PowerSeries.C c *
        (PowerSeries.map (algebraMap ℚ ℂ) U * S) at hc
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hc
  have ht := congrArg lpsOriginalRationalSeriesRetraction hscaled
  rw [lpsOriginalRationalSeriesRetraction_mul_map,
    lpsOriginalRationalSeriesRetraction_mul_map] at ht
  have hR := transfer a
  have hB := transfer b
  change lpsOriginalRationalSeriesRetraction (PowerSeries.C c * R) =
    ∑ i, PowerSeries.C (aq i) * T i at hR
  change lpsOriginalRationalSeriesRetraction (PowerSeries.C c * S) =
    ∑ i, PowerSeries.C (bq i) * T i at hB
  rw [hR, hB] at ht
  refine ⟨aq, bq, by simpa only [mul_comm] using ht, ?_⟩
  intro hz
  have hcoef := congrArg (fun V : PowerSeries ℚ => V.coeff n) hB
  rw [hz, map_zero] at hcoef
  simp only [lpsOriginalRationalSeriesRetraction, PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul] at hcoef
  have hunit : c * S.coeff n = 1 := inv_mul_cancel₀ hn
  rw [hunit, lpsOriginalRationalRetraction_one] at hcoef
  exact one_ne_zero hcoef
end QEC.Coding.TannerLiftedProduct
