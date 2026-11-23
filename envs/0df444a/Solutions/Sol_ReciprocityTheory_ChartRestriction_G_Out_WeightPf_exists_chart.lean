-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.WeightPf.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:47.604362+00:00
-- url     : https://prove2.me/submissions/466368fe-8d39-43c9-b54a-baf318e73b56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.WeightPf
theorem _root_.solution {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : X) : ∃ i, y ∈ L.U i := by
  have : y ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using this
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
