-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_toJ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:03:04.858145+00:00
-- url     : https://prove2.me/submissions/9e54883b-1ba8-406d-b95b-7c61a78e55a3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_chart
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalSchemeLevelChartMap_toJ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_chart


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN =
    lpsOriginalIntegerNormalGluedToProjectiveJ M hM := by
  apply Multicoequalizer.hom_ext
  intro b
  change Bool at b
  change lpsOriginalIntegerNormalGluedChartMap M hM b ≫
      (lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
        lpsOriginalIntegerNormalGluedToProjectiveJ N hN) =
    lpsOriginalIntegerNormalGluedChartMap M hM b ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ M hM
  rw [← Category.assoc, lpsOriginalIntegerNormalGluedForgetLevel_chart,
    Category.assoc, lpsOriginalIntegerNormalGluedToProjectiveJ_chart,
    lpsOriginalIntegerNormalGluedToProjectiveJ_chart]
  exact lpsOriginalIntegerNormalSchemeLevelChartMap_toJ N M hNM h4N hN hM b
end QEC.Coding.TannerLiftedProduct
