-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_infinity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:55:58.123413+00:00
-- url     : https://prove2.me/submissions/762c55f5-1f9d-4cf4-8ee6-f436123d681c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroChartToJLine_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJCharts_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN ⁻¹'
      Set.range (lpsOriginalIntegerProjectiveJChartMap true) =
    Set.range (lpsOriginalIntegerNormalGluedChartMap N hN true) := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨b,z,hz⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
    cases b with
    | false =>
      have h : lpsOriginalIntegerProjectiveJChartMap true y =
        lpsOriginalIntegerProjectiveJChartMap false
          (lpsOriginalIntegerNormalZeroChartToJLine N hN z) := by
        rw [hy,← hz,lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply]
        rfl
      obtain ⟨v,hv1,hv0⟩ := Scheme.exists_preimage_of_isPullback
        lpsOriginalIntegerProjectiveJCharts_pullback.flip y
        (lpsOriginalIntegerNormalZeroChartToJLine N hN z) h
      obtain ⟨w,hw0,_⟩ := Scheme.exists_preimage_of_isPullback
        (lpsOriginalIntegerNormalZeroChartToJLine_pullback N hN) z v hv0.symm
      refine ⟨lpsOriginalIntegerNormalSchemeOverlapMap N hN true w,?_⟩
      calc
        lpsOriginalIntegerNormalGluedChartMap N hN true
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN true w) =
          lpsOriginalIntegerNormalGluedChartMap N hN false
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN false w) :=
          congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
            lpsOriginalIntegerNormalGluedScheme N hN => f w)
            (lpsOriginalIntegerNormalGluedOverlap_agreement N hN).symm
        _ = lpsOriginalIntegerNormalGluedChartMap N hN false z :=
          congrArg (lpsOriginalIntegerNormalGluedChartMap N hN false) hw0
        _ = x := hz
    | true => exact ⟨z,hz⟩
  · rintro ⟨z,rfl⟩
    refine ⟨lpsOriginalIntegerNormalInfinityChartToJLine N hN z,?_⟩
    exact (lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply N hN true z).symm
end QEC.Coding.TannerLiftedProduct
