-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartBaseChangeIso_complexProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:04:42.851461+00:00
-- url     : https://prove2.me/submissions/3da0f10e-f4bd-476b-8312-a70523fbf180

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalizationAffineBaseChangeIso_constantRingHomProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalizationAffineBaseChangeIso_constantRingHomProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
    (lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom ≫ pullback.fst _ _ =
      lpsOriginalComplexChartToSpecC N hN b := by
  cases b with
  | false =>
    simpa only [lpsOriginalComplexNormalChartBaseChangeIso, Iso.trans_hom, Category.assoc,
      pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id,
      lpsOriginalComplexChartToSpecC] using
        (lpsOriginalZeroNormalizationAffineBaseChangeIso_constantRingHomProjection N hN)
  | true =>
    simpa only [lpsOriginalComplexNormalChartBaseChangeIso, Iso.trans_hom, Category.assoc,
      pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id,
      lpsOriginalComplexChartToSpecC] using
        (lpsOriginalInfinityNormalizationAffineBaseChangeIso_constantRingHomProjection N hN)
end QEC.Coding.TannerLiftedProduct
