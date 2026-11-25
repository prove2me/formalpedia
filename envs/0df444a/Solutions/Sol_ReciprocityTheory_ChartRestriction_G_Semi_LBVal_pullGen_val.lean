-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LBVal.pullGen_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:28:42.340417+00:00
-- url     : https://prove2.me/submissions/eea01dc1-5129-4601-a3e2-826efc38f267

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LBVal_rres

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
  CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LBVal
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Semi.LBVal
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) (W : Z.Opens) (hW : W ≤ LB.wchart L (fun k => h ≫ φ k) j) :
    (Z.presheaf.map (homOfLE hW).op).hom ((LB.pullGen L φ ε c h).s j).val =
      (h.appLE (LB.wchart L φ j) W (hW.trans (wchart_pull_le L φ h j))).hom (c.s j).val := by
  exact rres (wchart_pull_le L φ h j) hW ((h.app (LB.wchart L φ j)).hom (c.s j).val)
end ReciprocityTheory.ChartRestriction.G.Semi.LBVal
