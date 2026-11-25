-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.app_eq_zero_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:40.6639+00:00
-- url     : https://prove2.me/submissions/4c2309b8-2ab3-4f4f-b8fa-1473d0fa1b83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenLevel

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X Y Z : Scheme.{0}} {f : X ⟶ Z} {g : X ⟶ Y} {h : Y ⟶ Z} (hf : g ≫ h = f)
    (W : Z.Opens) (x : Γ(Z, W)) (hx : g.app (h ⁻¹ᵁ W) (h.app W x) = 0) : f.app W x = 0 := by
  subst hf
  first
  | exact hx
  | (rw [Scheme.comp_app]; exact hx)
  | (simp only [Scheme.comp_app, CommRingCat.comp_apply]; exact hx)
end ReciprocityTheory.ChartRestriction.G.DVR.TG
