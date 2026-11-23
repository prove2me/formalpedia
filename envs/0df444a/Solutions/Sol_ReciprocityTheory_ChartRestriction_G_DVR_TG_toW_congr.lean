-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:43.11932+00:00
-- url     : https://prove2.me/submissions/e33b5efd-a09a-4fb7-84ab-eedb318e83ca

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
theorem _root_.solution {X : Scheme.{0}} {p p' : X ⟶ Spec (CommRingCat.of R)} (h : p = p') (W : X.Opens) (r : R) :
    toW p W r = toW p' W r := by subst h; rfl
end ReciprocityTheory.ChartRestriction.G.DVR.TG
