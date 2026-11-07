-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:05:37.787966+00:00
-- url     : https://prove2.me/submissions/dec0fd78-b1a1-4249-ab2d-67d72596d126

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalChartProjection_finite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_chart_pullback

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) :
    IsFinite (lpsOriginalIntegerNormalGluedToProjectiveJ N hN) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P:=@IsFinite)
    lpsOriginalIntegerProjectiveJGlueData.openCover).mpr
  intro b
  let := lpsOriginalIntegerNormalChartProjection_finite N hN b
  have h := lpsOriginalIntegerNormalGluedToProjectiveJ_chart_pullback N hN b
  change IsFinite (pullback.snd (lpsOriginalIntegerNormalGluedToProjectiveJ N hN)
    (lpsOriginalIntegerProjectiveJChartMap b))
  rw [← h.isoPullback_inv_snd]
  infer_instance
end QEC.Coding.TannerLiftedProduct
