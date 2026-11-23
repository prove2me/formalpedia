-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:27.46838+00:00
-- url     : https://prove2.me/submissions/e143ec78-9d77-41d0-aa53-d4fad7fd261e

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
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) {V W : X.Opens} (h : W ≤ V) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (toW p V r) = toW p W r := by
  simp only [toW, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
end ReciprocityTheory.ChartRestriction.G.DVR.TG
