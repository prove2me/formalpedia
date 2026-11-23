-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.app_toW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:16.205803+00:00
-- url     : https://prove2.me/submissions/70365c34-af4f-40d7-9f51-1ad1941990d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (f : Y ⟶ X) (W : X.Opens) (r : R) :
    (f.app W).hom (toW p W r) = toW (f ≫ p) (f ⁻¹ᵁ W) r := by
  simp only [toW, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
end ReciprocityTheory.ChartRestriction.G.DVR.TG
