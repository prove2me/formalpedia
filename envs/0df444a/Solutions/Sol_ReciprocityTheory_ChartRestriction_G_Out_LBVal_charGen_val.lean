-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.LBVal.charGen_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:48.77483+00:00
-- url     : https://prove2.me/submissions/33d623bc-85b1-4ae2-8096-7428aa332522

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.LBVal
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.LBVal
theorem _root_.solution {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {Z : Scheme.{0}}
    (L : LB Z) (χ : X) (j : PEmpty → L.ι) (W : (splitTorus S X ⊗ G).left.Opens)
    (hW : W ≤ LB.wchart L (Y := (splitTorus S X ⊗ G).left) (K := PEmpty) PEmpty.elim j) :
    ((splitTorus S X ⊗ G).left.presheaf.map (homOfLE hW).op).hom ((charGen X G L χ).s j).val =
      ((splitTorus S X ⊗ G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP X G χ) := by
  have p : LB.wchart L (Y := (splitTorus S X ⊗ G).left) (K := PEmpty) PEmpty.elim j ≤
      (fst (splitTorus S X) G).left ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine (Semi.LBVal.rres p hW _).trans ?_
  all_goals rfl
end ReciprocityTheory.ChartRestriction.G.Out.LBVal
