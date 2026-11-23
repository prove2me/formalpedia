-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.pullGen_s_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:37.561953+00:00
-- url     : https://prove2.me/submissions/5e1c6a43-10ff-452f-bcc5-39fe3bd297ed

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
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) :
    ((LB.pullGen L φ ε c h).s j).val =
      (h.appLE (LB.wchart L φ j) (LB.wchart L (fun k => h ≫ φ k) j)
        (LBVal.wchart_pull_le L φ h j)).hom (c.s j).val := by
  rfl
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
