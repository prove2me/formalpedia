-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LBVal.mulGen_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:28:37.023807+00:00
-- url     : https://prove2.me/submissions/3076c103-2afd-4b39-b73e-8d565cd3912e

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
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι)
    (W : Y.Opens) (hW : W ≤ LB.wchart L (Sum.elim φ φ') j) :
    (Y.presheaf.map (homOfLE hW).op).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      (Y.presheaf.map (homOfLE (hW.trans (fun _ hy => Set.mem_iInter.2 fun k =>
          Set.mem_iInter.1 hy (Sum.inl k)))).op).hom (t.s (j ∘ Sum.inl)).val *
      (Y.presheaf.map (homOfLE (hW.trans (fun _ hy => Set.mem_iInter.2 fun k =>
          Set.mem_iInter.1 hy (Sum.inr k)))).op).hom (t'.s (j ∘ Sum.inr)).val := by
  have ha : LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have hb : LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  change (Y.presheaf.map (homOfLE hW).op).hom
      ((Y.presheaf.map (homOfLE ha).op).hom (t.s (j ∘ Sum.inl)).val *
        (Y.presheaf.map (homOfLE hb).op).hom (t'.s (j ∘ Sum.inr)).val) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (rres ha hW _) (rres hb hW _)
end ReciprocityTheory.ChartRestriction.G.Semi.LBVal
