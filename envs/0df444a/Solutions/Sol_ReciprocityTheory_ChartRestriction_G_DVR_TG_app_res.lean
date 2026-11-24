-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.app_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:53.676418+00:00
-- url     : https://prove2.me/submissions/9f8c607d-f728-4491-a2e9-e8405a74f111

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
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) =
      (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR.TG
