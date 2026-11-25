-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_app_comp__dd8acccb3343
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:54:30.596349+00:00
-- url     : https://prove2.me/submissions/bf60cf64-3e6a-409e-b673-373b5e917ba0

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
theorem _root_.solution {Z Y X : Scheme.{0}} (h : Z ⟶ Y) (ψ : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    {V : Z.Opens} (hW : W ≤ ψ ⁻¹ᵁ U) (hV : V ≤ h ⁻¹ᵁ W) (hV' : V ≤ (h ≫ ψ) ⁻¹ᵁ U) (x : Γ(X, U)) :
    rs hV ((h.app W).hom (rs hW ((ψ.app U).hom x))) = rs hV' (((h ≫ ψ).app U).hom x) := by
  rw [app_rs, rs_rs, Scheme.Hom.comp_app]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
