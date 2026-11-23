-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.WeightPf.mem_of_finset_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:04.96562+00:00
-- url     : https://prove2.me/submissions/9dfc5862-df48-43e8-8e69-f2746350e6cd

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
theorem _root_.solution {Y : Scheme.{0}} {κ : Type} {s : Finset κ} {F : κ → Y.Opens} {y : Y}
    (h : y ∈ s.inf F) {i : κ} (hi : i ∈ s) : y ∈ F i :=
  (Finset.inf_le hi : s.inf F ≤ F i) h
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
