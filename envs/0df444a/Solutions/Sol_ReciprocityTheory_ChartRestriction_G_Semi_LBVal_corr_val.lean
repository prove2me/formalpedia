-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LBVal.corr_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:28:30.280843+00:00
-- url     : https://prove2.me/submissions/fd0bf267-1960-4796-9e31-cdb987b8ca6a

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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (hc : LB.Gen.Corr L φ ε φ' ε' t t') (j : K → L.ι) (j' : K' → L.ι) (c1 : LB.Coh L φ j)
    (c2 : LB.Coh L φ' j') (c3 : ∀ k k', φ k = φ' k' → j k = j' k') (W : Y.Opens)
    (hW : W ≤ LB.wchart L φ j ⊓ LB.wchart L φ' j') :
    (Y.presheaf.map (homOfLE (hW.trans inf_le_left)).op).hom (t.s j).val =
      (Y.presheaf.map (homOfLE (hW.trans inf_le_right)).op).hom (t'.s j').val := by
  have e := congrArg (fun u : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ' j')ˣ =>
    (Y.presheaf.map (homOfLE hW).op).hom u.val) (hc j j' c1 c2 c3)
  exact (rres inf_le_left hW _).symm.trans (e.trans (rres inf_le_right hW _))
end ReciprocityTheory.ChartRestriction.G.Semi.LBVal
