-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gw_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:26:10.68823+00:00
-- url     : https://prove2.me/submissions/e6993191-f223-48ad-9c7a-36ce88fec993

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
private lemma res_pullU_comp_factor_through_open {X Y Z : Scheme.{0}} (h : Z ⟶ Y) (φ : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    {T : Z.Opens} (hb : W ≤ φ ⁻¹ᵁ U) (ha : T ≤ (h ≫ φ) ⁻¹ᵁ U) (hW : T ≤ h ⁻¹ᵁ W) (g : Γ(X, U)ˣ) :
    res ha (pullU (h ≫ φ) U g) = res hW (pullU h W (res hb (pullU φ U g))) := by
  rw [pullU_res, res_res', pullU_comp]
  rfl
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Z ⟶ Y) (j j' : K → L.ι)
    (hW : LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ k) j' ≤
      h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    gw L (fun k => h ≫ φ k) ε j j' = res hW (pullU h _ (gw L φ ε j j')) := by
  simp only [gw, map_prod, map_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  beta_reduce
  exact res_pullU_comp_factor_through_open (U := L.U (j k) ⊓ L.U (j' k)) (W := LB.wchart L φ j ⊓ LB.wchart L φ j') h (φ k) _ _ hW
    (L.g (j k) (j' k))
end ReciprocityTheory.ChartRestriction.G.DVR
