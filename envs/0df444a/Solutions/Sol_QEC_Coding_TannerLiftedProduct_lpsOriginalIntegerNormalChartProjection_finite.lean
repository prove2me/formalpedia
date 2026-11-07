-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalChartProjection_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:56:17.447601+00:00
-- url     : https://prove2.me/submissions/71ed9653-33a6-4f40-986f-62910933faf3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroChartToJLine_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityChartToJLine_finite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    IsFinite (lpsOriginalIntegerNormalChartProjection N hN b) := by
  cases b with
  | false => exact lpsOriginalIntegerNormalZeroChartToJLine_finite N hN
  | true => exact lpsOriginalIntegerNormalInfinityChartToJLine_finite N hN
end QEC.Coding.TannerLiftedProduct
