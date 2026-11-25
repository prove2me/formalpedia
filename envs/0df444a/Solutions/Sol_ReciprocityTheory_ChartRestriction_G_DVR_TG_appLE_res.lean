-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.appLE_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:01.880002+00:00
-- url     : https://prove2.me/submissions/c38ac658-fe28-4f57-a6b7-bebfe08b689b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenLevel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv

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
theorem _root_.solution {X Y : Scheme.{0}} (i0 : X ⟶ Y) {V1 W : Y.Opens} {V0 : X.Opens} (hV : V0 ≤ i0 ⁻¹ᵁ V1)
    (h1 : V1 ≤ W) (h0 : V0 ≤ i0 ⁻¹ᵁ W) (y : Γ(Y, W)) :
    (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y) =
      (X.presheaf.map (homOfLE h0).op).hom ((i0.app W).hom y) := by
  have e1 := i0.map_appLE hV (homOfLE h1).op
  have e2 : i0.app W ≫ X.presheaf.map (homOfLE h0).op = i0.appLE W V0 h0 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  calc (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y)
      = (Y.presheaf.map (homOfLE h1).op ≫ i0.appLE V1 V0 hV).hom y := rfl
    _ = (i0.appLE W V0 h0).hom y := by rw [e1]
    _ = (i0.app W ≫ X.presheaf.map (homOfLE h0).op).hom y := by rw [e2]
    _ = _ := rfl
end ReciprocityTheory.ChartRestriction.G.DVR.TG
