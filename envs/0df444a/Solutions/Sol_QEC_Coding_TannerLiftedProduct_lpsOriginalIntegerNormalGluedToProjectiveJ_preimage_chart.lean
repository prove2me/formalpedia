-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:00:48.105317+00:00
-- url     : https://prove2.me/submissions/827502ff-81d9-42f0-b65b-0f47e1b6b779

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_infinity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN ⁻¹'
      Set.range (lpsOriginalIntegerProjectiveJChartMap b) =
    Set.range (lpsOriginalIntegerNormalGluedChartMap N hN b) := by
  cases b with
  | false => exact lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_zero N hN
  | true => exact lpsOriginalIntegerNormalGluedToProjectiveJ_preimage_infinity N hN
end QEC.Coding.TannerLiftedProduct
