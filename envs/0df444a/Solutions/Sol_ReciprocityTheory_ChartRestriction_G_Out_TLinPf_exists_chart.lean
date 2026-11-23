-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:00.372301+00:00
-- url     : https://prove2.me/submissions/9dd417ed-99f1-4660-ae82-3e55a05afef5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : X) : ∃ i, y ∈ L.U i := by
  have : y ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using this
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
