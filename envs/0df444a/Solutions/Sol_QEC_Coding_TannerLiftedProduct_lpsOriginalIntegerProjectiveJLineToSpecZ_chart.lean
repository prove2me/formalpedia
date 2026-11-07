-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:53:36.327389+00:00
-- url     : https://prove2.me/submissions/32b2d229-7a3e-439d-9a3f-002a8fafc7b3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (b : Bool) :
    lpsOriginalIntegerProjectiveJChartMap b ≫
      lpsOriginalIntegerProjectiveJLineToSpecZ =
    lpsOriginalIntegerProjectiveJChartToSpecZ :=
  Multicoequalizer.π_desc _ _ _ _ _
end QEC.Coding.TannerLiftedProduct
