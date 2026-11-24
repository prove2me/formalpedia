-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.WeightPf.act_left_pG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:31.379815+00:00
-- url     : https://prove2.me/submissions/61a14b8d-1414-412d-bb41-3f57bc986400

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_q

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
theorem _root_.solution : (act g).left ≫ g.pG.left = (snd (Te D I e) (thickObj R I e G)).left ≫ g.pG.left := by
  have h : (act g).left ≫ g.q.left = (snd (Te D I e) (thickObj R I e G)).left ≫ g.q.left :=
    congrArg (fun f => f.left) (act_q g)
  simp only [GtCoord.pG, Over.comp_left, Over.map_map_left]
  rw [reassoc_of% h]
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
