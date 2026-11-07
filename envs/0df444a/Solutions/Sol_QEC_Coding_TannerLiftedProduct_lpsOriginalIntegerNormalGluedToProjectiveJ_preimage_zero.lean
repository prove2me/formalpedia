-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:56:54.896543+00:00
-- url     : https://prove2.me/submissions/ddf41301-2270-4540-b05f-322150064aab

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityChartToJLine_pullback
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
      Set.range (lpsOriginalIntegerProjectiveJChartMap false) =
    Set.range (lpsOriginalIntegerNormalGluedChartMap N hN false) := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨b,z,hz⟩ := lpsOriginalIntegerNormalGluedChartMap_cover N hN x
    cases b with
    | false => exact ⟨z,hz⟩
    | true =>
      have h : lpsOriginalIntegerProjectiveJChartMap false y =
        lpsOriginalIntegerProjectiveJChartMap true
          (lpsOriginalIntegerNormalInfinityChartToJLine N hN z) := by
        rw [hy,← hz,lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply]
        rfl
      obtain ⟨v,hv0,hv1⟩ := Scheme.exists_preimage_of_isPullback
        lpsOriginalIntegerProjectiveJCharts_pullback y
        (lpsOriginalIntegerNormalInfinityChartToJLine N hN z) h
      obtain ⟨w,hw1,_⟩ := Scheme.exists_preimage_of_isPullback
        (lpsOriginalIntegerNormalInfinityChartToJLine_pullback N hN) z v hv1.symm
      refine ⟨lpsOriginalIntegerNormalSchemeOverlapMap N hN false w,?_⟩
      calc
        lpsOriginalIntegerNormalGluedChartMap N hN false
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN false w) =
          lpsOriginalIntegerNormalGluedChartMap N hN true
            (lpsOriginalIntegerNormalSchemeOverlapMap N hN true w) :=
          congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
            lpsOriginalIntegerNormalGluedScheme N hN => f w)
            (lpsOriginalIntegerNormalGluedOverlap_agreement N hN)
        _ = lpsOriginalIntegerNormalGluedChartMap N hN true z :=
          congrArg (lpsOriginalIntegerNormalGluedChartMap N hN true) hw1
        _ = x := hz
  · rintro ⟨z,rfl⟩
    refine ⟨lpsOriginalIntegerNormalZeroChartToJLine N hN z,?_⟩
    exact (lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply N hN false z).symm
end QEC.Coding.TannerLiftedProduct
