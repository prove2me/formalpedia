-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rs_app_mulGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:41.64898+00:00
-- url     : https://prove2.me/submissions/0d95f505-643c-4a55-b85a-40850c2a1994

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


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
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {X Y Y' Z : Scheme.{0}} (L : LB X) {K₁ K₂ K₃ K K' : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃]
  [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (φ : K → (Y' ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι)
    (q : Z ⟶ Y') {O : Z.Opens} (h : O ≤ q ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j)
    (h₁ : O ≤ q ⁻¹ᵁ LB.wchart L φ (j ∘ Sum.inl)) (h₂ : O ≤ q ⁻¹ᵁ LB.wchart L φ' (j ∘ Sum.inr)) :
    rs h ((q.app _).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val) =
      rs h₁ ((q.app _).hom (t.s (j ∘ Sum.inl)).val) * rs h₂ ((q.app _).hom (t'.s (j ∘ Sum.inr)).val) := by
  simp only [LB.mulGen, Units.val_mul, map_mul, rs_mul]
  congr 1
  · exact (congrArg (rs h) (app_rs q _ (t.s (j ∘ Sum.inl)).val)).trans (rs_rs _ _ _)
  · exact (congrArg (rs h) (app_rs q _ (t'.s (j ∘ Sum.inr)).val)).trans (rs_rs _ _ _)
end ReciprocityTheory.ChartRestriction.G.DVR
