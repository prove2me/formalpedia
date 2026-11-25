-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rs_app_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:34.774557+00:00
-- url     : https://prove2.me/submissions/61a7ac7f-d77a-4cab-a081-66776c5b49c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf

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
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Z Y X : Scheme.{0}} (h : Z ⟶ Y) (ψ : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    {V : Z.Opens} (hW : W ≤ ψ ⁻¹ᵁ U) (hV : V ≤ h ⁻¹ᵁ W) (hV' : V ≤ (h ≫ ψ) ⁻¹ᵁ U) (x : Γ(X, U)) :
    rs hV ((h.app W).hom (rs hW ((ψ.app U).hom x))) = rs hV' (((h ≫ ψ).app U).hom x) := by
  change (ψ.appLE U W hW ≫ h.appLE W V hV).hom x = ((h ≫ ψ).appLE U V hV').hom x
  first
    | rw [Scheme.Hom.appLE_comp_appLE]
    | rw [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]
end ReciprocityTheory.ChartRestriction.G.DVR
