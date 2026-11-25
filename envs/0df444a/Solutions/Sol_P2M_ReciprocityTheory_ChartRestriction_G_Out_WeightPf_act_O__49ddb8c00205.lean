-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_O__49ddb8c00205
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:42.893482+00:00
-- url     : https://prove2.me/submissions/8e86ca2c-fc5e-41f4-9b74-d00e731d09a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_map_act_pG

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
theorem _root_.solution (χ : D.X) (k : Fin 4) :
    (act g).left ≫ D.Oφ g.pG χ k = (snd (Te D I e) (thickObj R I e G)).left ≫ D.Oφ g.pG χ k := by
  calc (act g).left ≫ D.Oφ g.pG χ k
      = D.Oφ ((Over.map (thick R I e)).map (act g) ≫ g.pG) χ k :=
        Oφ_comp (D := D) ((Over.map (thick R I e)).map (act g)) g.pG χ k
    _ = D.Oφ ((Over.map (thick R I e)).map (snd (Te D I e) (thickObj R I e G)) ≫ g.pG) χ k := by
        rw [map_act_pG g]
    _ = (snd (Te D I e) (thickObj R I e G)).left ≫ D.Oφ g.pG χ k :=
        (Oφ_comp (D := D) ((Over.map (thick R I e)).map (snd (Te D I e) (thickObj R I e G))) g.pG χ k).symm
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
