-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalRationalFibre_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:47:02.191509+00:00
-- url     : https://prove2.me/submissions/e5fbe6bc-0436-4506-a540-131327423429

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalRationalChart_smooth
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
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    Smooth (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (lpsOriginalIntegerNormalGluedToSpecZ N hpos)) := by
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Smooth.{0})
      (Q := @RingHom.Smooth.{0, 0})
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Smooth.{0})
    (f := pullback.fst _ _)
    (Scheme.Pullback.openCoverOfRight
      (lpsOriginalIntegerNormalSchemeGlueData N hpos).openCover
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (lpsOriginalIntegerNormalGluedToSpecZ N hpos))).mpr
  intro b
  change Bool at b
  change Smooth (pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
    (lpsOriginalIntegerNormalGluedChartMap N hpos b ≫
      lpsOriginalIntegerNormalGluedToSpecZ N hpos)
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
    (lpsOriginalIntegerNormalGluedToSpecZ N hpos)
    (𝟙 _) (lpsOriginalIntegerNormalGluedChartMap N hpos b) (𝟙 _)
    (by simp) (by simp) ≫ pullback.fst _ _)
  simp only [pullback.map, pullback.lift_fst, Category.comp_id]
  exact lpsOriginalIntegerNormalRationalChart_smooth N hpos b
end QEC.Coding.TannerLiftedProduct
