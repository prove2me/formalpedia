-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicValuationRing_formallySmooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:46:55.081355+00:00
-- url     : https://prove2.me/submissions/5e68b8d4-0958-408c-b09d-94dbb0ef0472

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dvr_formallySmoothCharZero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicValuationRing_essFiniteType
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing


set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    let V := Valuation.valuationSubring
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
    letI : Algebra ℂ V :=
      (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
    Algebra.FormallySmooth ℂ V := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let V := Valuation.valuationSubring
    (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
  let : Algebra ℂ V :=
    (lpsOriginalComplexConstantsToMeromorphicValuationRing N hpos hN x).toAlgebra
  let : IsDiscreteValuationRing V :=
    lpsOriginalMeromorphicValuationRing_isDiscreteValuationRing N hpos hN x
  let : Algebra.EssFiniteType ℂ V :=
    lpsOriginalMeromorphicValuationRing_essFiniteType N hpos hN x
  exact QEC.Coding.AlgebraicGeometry.dvr_formallySmoothCharZero ℂ V
end QEC.Coding.TannerLiftedProduct
