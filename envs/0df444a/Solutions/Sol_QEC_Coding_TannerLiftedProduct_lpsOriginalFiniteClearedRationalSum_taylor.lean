-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedRationalSum_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:18:24.531189+00:00
-- url     : https://prove2.me/submissions/534d94b6-30be-417d-abdd-010fc416cfe3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_const_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_sum
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
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ) :
    lpsOriginalTaylorSeries (lpsOriginalFiniteClearedRationalSum M B u v a) =
      PowerSeries.map (algebraMap ℚ ℂ)
        (∑ i, PowerSeries.C (a i) * lpsOriginalClearedFormalMonomial M hM B (u i) (v i)) := by
  classical
  unfold lpsOriginalFiniteClearedRationalSum
  rw [lpsOriginalTaylorSeries_sum Finset.univ
    (fun i => fun q => (a i : ℂ) * lpsOriginalClearedMonomial M B (u i) (v i) q)
    (fun i _hi => analyticAt_const.mul
      (lpsOriginalClearedMonomial_analytic M hM B (u i) (v i)))]
  simp only [map_sum, map_mul, PowerSeries.map_C]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lpsOriginalTaylorSeries_const_mul, lpsOriginalClearedMonomial_taylor M hM]
  rfl
end QEC.Coding.TannerLiftedProduct
