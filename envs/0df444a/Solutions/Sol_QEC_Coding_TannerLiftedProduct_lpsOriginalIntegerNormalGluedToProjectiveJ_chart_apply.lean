-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_chart_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:01:09.596878+00:00
-- url     : https://prove2.me/submissions/eced21ff-7856-49b3-b77b-a91277aab77b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedToProjectiveJ_chart

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) (b : Bool)
    (y : lpsOriginalIntegerNormalSchemeChart N hN b) :
    lpsOriginalIntegerNormalGluedToProjectiveJ N hN
      (lpsOriginalIntegerNormalGluedChartMap N hN b y) =
      lpsOriginalIntegerNormalChartToProjectiveJ N hN b y := by
  exact congrArg (fun f : lpsOriginalIntegerNormalSchemeChart N hN b ⟶
    lpsOriginalIntegerProjectiveJLine => f y)
    (lpsOriginalIntegerNormalGluedToProjectiveJ_chart N hN b)
end QEC.Coding.TannerLiftedProduct
