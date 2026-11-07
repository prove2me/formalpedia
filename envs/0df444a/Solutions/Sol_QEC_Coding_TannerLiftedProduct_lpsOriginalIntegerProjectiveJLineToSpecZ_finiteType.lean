-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:56:51.756973+00:00
-- url     : https://prove2.me/submissions/ee03a834-1274-440a-bbb9-a2ec5ccf08bf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_chart
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJChartToSpecZ_finiteType

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    LocallyOfFiniteType lpsOriginalIntegerProjectiveJLineToSpecZ := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P:=@LocallyOfFiniteType)
    lpsOriginalIntegerProjectiveJGlueData.openCover).mpr
  intro b
  change LocallyOfFiniteType (lpsOriginalIntegerProjectiveJChartMap b ≫
    lpsOriginalIntegerProjectiveJLineToSpecZ)
  rw [lpsOriginalIntegerProjectiveJLineToSpecZ_chart]
  exact lpsOriginalIntegerProjectiveJChartToSpecZ_finiteType
end QEC.Coding.TannerLiftedProduct
