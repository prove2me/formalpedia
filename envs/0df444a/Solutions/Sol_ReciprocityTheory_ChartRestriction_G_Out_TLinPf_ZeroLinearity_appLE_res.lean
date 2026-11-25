-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.appLE_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:17:21.537986+00:00
-- url     : https://prove2.me/submissions/b774077a-a44e-48f9-8a3e-b7a98fde699c

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
theorem _root_.solution (f : Z ⟶ Y) {U V : Y.Opens} (hUV : V ≤ U) {W' : Z.Opens} (hW : W' ≤ f ⁻¹ᵁ V)
    (x : Γ(Y, U)ˣ) :
    (f.appLE V W' hW).hom (res hUV x).val =
      (f.appLE U W' (hW.trans (f.preimage_mono hUV))).hom x.val := by
  change (Y.presheaf.map (homOfLE hUV).op ≫ f.appLE V W' hW).hom x.val = _
  rw [Scheme.Hom.map_appLE]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
