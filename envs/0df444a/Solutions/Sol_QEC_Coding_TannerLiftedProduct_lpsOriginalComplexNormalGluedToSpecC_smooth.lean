-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedToSpecC_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:47:00.519124+00:00
-- url     : https://prove2.me/submissions/057b0559-cbe7-4e23-9c2a-25d87bbb5740

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexChartToSpecC_smooth

set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    Smooth (lpsOriginalComplexNormalGluedToSpecC N hpos) := by
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Smooth.{0})
      (Q := @RingHom.Smooth.{0, 0})
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Smooth.{0})
    (f := lpsOriginalComplexNormalGluedToSpecC N hpos)
    (lpsOriginalComplexNormalSchemeGlueData N hpos).openCover).mpr
  intro b
  change Bool at b
  change Smooth (lpsOriginalComplexNormalGluedChartMap N hpos b ≫
    lpsOriginalComplexNormalGluedToSpecC N hpos)
  rw [lpsOriginalComplexNormalGluedToSpecC_chart]
  exact lpsOriginalComplexChartToSpecC_smooth N hpos b
end QEC.Coding.TannerLiftedProduct
