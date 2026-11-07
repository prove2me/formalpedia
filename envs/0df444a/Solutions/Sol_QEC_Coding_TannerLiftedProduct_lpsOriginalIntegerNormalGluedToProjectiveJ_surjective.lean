-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:07:44.420645+00:00
-- url     : https://prove2.me/submissions/77e22ef0-00dc-41d2-ae4c-f71b8d8beafd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroChartToJLine_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityChartToJLine_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalChartProjection_comp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_chart
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJChartMap_cover


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalGluedToProjectiveJ N hN) := by
  constructor
  intro x
  obtain ⟨b, y, rfl⟩ := lpsOriginalIntegerProjectiveJChartMap_cover x
  have hs : Surjective (lpsOriginalIntegerNormalChartProjection N hN b) := by
    cases b with
    | false => exact lpsOriginalIntegerNormalZeroChartToJLine_surjective N hN
    | true => exact lpsOriginalIntegerNormalInfinityChartToJLine_surjective N hN
  obtain ⟨z, hz⟩ := Scheme.Hom.surjective (lpsOriginalIntegerNormalChartProjection N hN b) y
  refine ⟨lpsOriginalIntegerNormalGluedChartMap N hN b z, ?_⟩
  have hc := lpsOriginalIntegerNormalGluedToProjectiveJ_chart N hN b
  have hp := lpsOriginalIntegerNormalChartProjection_comp N hN b
  exact congrArg (fun f : lpsOriginalIntegerNormalSchemeChart N hN b ⟶
    lpsOriginalIntegerProjectiveJLine => f z) (hc.trans hp.symm) |>.trans (congrArg _ hz)
end QEC.Coding.TannerLiftedProduct
