-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartBaseChangeIso_integerProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:04:39.822424+00:00
-- url     : https://prove2.me/submissions/a4120efb-13d8-4a8e-9949-fee438c6b711

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalizationAffineBaseChangeIso_integerRingHomProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalizationAffineBaseChangeIso_integerRingHomProjection
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
    (lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom ≫ pullback.snd _ _ =
      lpsOriginalComplexToIntegerChartMap N hN b := by
  cases b with
  | false =>
    simpa only [lpsOriginalComplexNormalChartBaseChangeIso, Iso.trans_hom, Category.assoc,
      pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
      lpsOriginalComplexToIntegerChartMap] using
        (lpsOriginalZeroNormalizationAffineBaseChangeIso_integerRingHomProjection N hN)
  | true =>
    simpa only [lpsOriginalComplexNormalChartBaseChangeIso, Iso.trans_hom, Category.assoc,
      pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
      lpsOriginalComplexToIntegerChartMap] using
        (lpsOriginalInfinityNormalizationAffineBaseChangeIso_integerRingHomProjection N hN)
end QEC.Coding.TannerLiftedProduct
