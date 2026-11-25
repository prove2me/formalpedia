-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.zz_0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:16.895208+00:00
-- url     : https://prove2.me/submissions/6946479f-6dac-4121-a4d8-a589540c10b9

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
variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (f g : B ⟶ B) [IsMonHom g]
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
theorem _root_.solution : zz B ≫ padd B (fst B B ≫ f) (snd B B) = f := by
  rw [zz, padd, ← Category.assoc, comp_lift]
  simpa using MonObj.lift_comp_one_right f
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
