-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalToIntegerBaseChange_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:08:01.961753+00:00
-- url     : https://prove2.me/submissions/3a2ee3f7-69f4-472c-a9d5-d0467ae126cb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalChartBaseChangeIso_integerProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalChartBaseChangeIso_complexProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalToIntegerBaseChange_complexProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalToIntegerBaseChange_integerProjection
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
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalComplexNormalGluedChartMap N hN b ≫
      lpsOriginalComplexNormalToIntegerBaseChange N hN =
    (lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom ≫
      (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, lpsOriginalComplexNormalToIntegerBaseChange_complexProjection,
      lpsOriginalComplexNormalGluedToSpecC_chart,
      lpsOriginalIntegerNormalComplexBaseChangeOpenCover, Scheme.Pullback.openCoverOfRight_f,
      pullback.map, pullback.lift_fst, Category.comp_id]
    change lpsOriginalComplexChartToSpecC N hN b =
      (lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom ≫ pullback.fst _ _
    exact (lpsOriginalComplexNormalChartBaseChangeIso_complexProjection N hN b).symm
  · simp only [Category.assoc, lpsOriginalComplexNormalToIntegerBaseChange_integerProjection,
      lpsOriginalComplexNormalGluedToIntegerNormal_chart,
      lpsOriginalIntegerNormalComplexBaseChangeOpenCover, Scheme.Pullback.openCoverOfRight_f,
      pullback.map, pullback.lift_snd, Category.comp_id]
    rw [← Category.assoc]
    change lpsOriginalComplexToIntegerChartMap N hN b ≫
      lpsOriginalIntegerNormalGluedChartMap N hN b =
      ((lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom ≫ pullback.snd _ _) ≫
        lpsOriginalIntegerNormalGluedChartMap N hN b
    rw [lpsOriginalComplexNormalChartBaseChangeIso_integerProjection]
end QEC.Coding.TannerLiftedProduct
