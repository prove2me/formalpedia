-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.WeightPf.cancel_sec_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:44:53.829096+00:00
-- url     : https://prove2.me/submissions/892be069-da39-40ff-845b-79d2bb254f7f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_sec_left_snd

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
theorem _root_.solution {Z : Scheme.{0}} {a b : (thickObj R I e G).left ⟶ Z}
    (h : (snd (Te D I e) (thickObj R I e G)).left ≫ a = (snd (Te D I e) (thickObj R I e G)).left ≫ b) :
    a = b := by
  calc a = ((sec (D := D) (G := G) (I := I) (e := e)).left ≫
          (snd (Te D I e) (thickObj R I e G)).left) ≫ a := by
        rw [sec_left_snd, Category.id_comp]
    _ = (sec (D := D) (G := G) (I := I) (e := e)).left ≫
          ((snd (Te D I e) (thickObj R I e G)).left ≫ a) := Category.assoc _ _ _
    _ = (sec (D := D) (G := G) (I := I) (e := e)).left ≫
          ((snd (Te D I e) (thickObj R I e G)).left ≫ b) := by rw [h]
    _ = b := by rw [← Category.assoc, sec_left_snd, Category.id_comp]
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
