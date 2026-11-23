-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_map_rfl__124873d90145
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:04.675827+00:00
-- url     : https://prove2.me/submissions/3269c17c-0556-4482-b169-7e0f4730e8ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq

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
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
theorem _root_.solution {V : Y.Opens} (x : Γ(Y, V)) :
    (Y.presheaf.map (homOfLE (le_rfl : V ≤ V)).op).hom x = x := by
  simp
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
