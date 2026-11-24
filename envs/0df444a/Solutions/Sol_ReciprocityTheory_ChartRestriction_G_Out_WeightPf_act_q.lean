-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.WeightPf.act_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:44.712821+00:00
-- url     : https://prove2.me/submissions/d3d2bdc5-2086-4cfa-af61-fbac427ca11e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_i_q

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
theorem _root_.solution : act g ≫ g.q = snd (Te D I e) (thickObj R I e G) ≫ g.q := by
  haveI : IsMonHom g.q := g.q_hom
  have hq : g.i ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := i_q g
  have hf : fst (Te D I e) (thickObj R I e G) ≫ toUnit (Te D I e) =
      toUnit (Te D I e ⊗ thickObj R I e G) := toUnit_unique _ _
  simp only [act, Category.assoc, IsMonHom.mul_hom, CartesianMonoidalCategory.lift_map_assoc, hq,
    reassoc_of% hq, reassoc_of% hf, MonObj.lift_comp_one_left]
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
