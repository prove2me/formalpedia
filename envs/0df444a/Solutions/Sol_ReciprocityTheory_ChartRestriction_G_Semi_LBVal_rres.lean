-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LBVal.rres
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:45.748599+00:00
-- url     : https://prove2.me/submissions/7f42f5a1-7a54-47c8-bfd7-3a92d3b0a71b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe

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
  CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LBVal
namespace ReciprocityTheory.ChartRestriction.G.Semi.LBVal
theorem _root_.solution {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  change (X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom x = _
  rw [← Functor.map_comp]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.G.Semi.LBVal
