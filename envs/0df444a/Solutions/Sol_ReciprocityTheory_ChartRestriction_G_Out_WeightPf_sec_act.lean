-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.WeightPf.sec_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:24:28.786802+00:00
-- url     : https://prove2.me/submissions/e3dda9e2-1ae1-4ac9-9f87-a3c232f14408

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct

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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace ReciprocityTheory.ChartRestriction.G.Out.WeightPf
theorem _root_.solution : sec (D := D) (G := G) (I := I) (e := e) ≫ act g = 𝟙 _ := by
  haveI : IsMonHom g.i := g.i_hom
  have h1 : sec (D := D) (G := G) (I := I) (e := e) ≫
      lift (fst (Te D I e) (thickObj R I e G) ≫ g.i) (snd (Te D I e) (thickObj R I e G)) =
      lift (toUnit (thickObj R I e G) ≫ η[thickObj R I e G]) (𝟙 _) := by
    simp only [sec, CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.lift_fst_assoc,
      CartesianMonoidalCategory.lift_snd, Category.assoc, IsMonHom.one_hom]
  rw [act, ← Category.assoc, h1, MonObj.lift_comp_one_left]
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
