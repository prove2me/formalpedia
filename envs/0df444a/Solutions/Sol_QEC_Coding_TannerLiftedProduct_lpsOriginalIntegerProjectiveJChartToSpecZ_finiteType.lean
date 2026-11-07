-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJChartToSpecZ_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:53:49.763199+00:00
-- url     : https://prove2.me/submissions/18628dad-2ad6-44df-a592-77c6aab59255

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
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    LocallyOfFiniteType lpsOriginalIntegerProjectiveJChartToSpecZ := by
  unfold lpsOriginalIntegerProjectiveJChartToSpecZ
  rw [HasRingHomProperty.Spec_iff (P:=@LocallyOfFiniteType)]
  change RingHom.FiniteType (Polynomial.C : ℤ →+* Polynomial ℤ)
  rw [← Polynomial.algebraMap_eq, RingHom.finiteType_algebraMap]
  infer_instance
end QEC.Coding.TannerLiftedProduct
