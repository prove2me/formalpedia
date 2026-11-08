-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalComplexBaseChangedCharts_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:59:50.554194+00:00
-- url     : https://prove2.me/submissions/f46a7e41-b8df-4c96-a235-46c755af7022

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_intersectionBaseChangedScalarFirst
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_scalarFirstBaseChangedMap_eq_pullbackMap
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
open QEC.Coding.AlgebraicGeometry.ChartBaseChange
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0 < N) :
    IsPullback (lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN false)
      (lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN true)
      ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f false)
      ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f true) := by
  let a := lpsOriginalIntegerNormalSchemeOverlapMap N hN false
  let b := lpsOriginalIntegerNormalSchemeOverlapMap N hN true
  let i := lpsOriginalIntegerNormalGluedChartMap N hN false
  let j := lpsOriginalIntegerNormalGluedChartMap N hN true
  let x := lpsOriginalIntegerNormalGluedToSpecZ N hN
  let t := Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ))
  have H := intersectionBaseChangedScalarFirst a b i j x t
    (lpsOriginalIntegerNormalCharts_pullback N hN)
  apply H.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · rfl
  · rfl
  · simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      lpsOriginalIntegerNormalComplexBaseChangeOpenCover, Scheme.Pullback.openCoverOfRight_f,
      Scheme.GlueData.openCover, lpsOriginalIntegerNormalGluedChartMap,
      a, b, i, j, x, t] using scalarFirstBaseChangedMap_eq_pullbackMap t (i ≫ x) x i rfl
  · simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      lpsOriginalIntegerNormalComplexBaseChangeOpenCover, Scheme.Pullback.openCoverOfRight_f,
      Scheme.GlueData.openCover, lpsOriginalIntegerNormalGluedChartMap,
      a, b, i, j, x, t] using scalarFirstBaseChangedMap_eq_pullbackMap t (j ≫ x) x j rfl
end QEC.Coding.TannerLiftedProduct
