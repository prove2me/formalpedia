-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rs_app_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:24.957517+00:00
-- url     : https://prove2.me/submissions/ceec76ab-760e-4471-9a0f-89fe89c18b67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
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
theorem _root_.solution {W : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε))
    (g : W ⟶ Y) (j : K → L.ι) (q : Z ⟶ W) {O : Z.Opens}
    (h : O ≤ q ⁻¹ᵁ LB.wchart L (fun k => g ≫ φ k) j) (h' : O ≤ (q ≫ g) ⁻¹ᵁ LB.wchart L φ j) :
    rs h ((q.app _).hom ((LB.pullGen L φ ε c g).s j).val) = rs h' (((q ≫ g).app _).hom (c.s j).val) :=
  (congrArg (rs h) (app_rs q (wchart_comp_le φ g j) ((g.app _).hom (c.s j).val))).trans (rs_rs _ _ _)
end ReciprocityTheory.ChartRestriction.G.DVR
