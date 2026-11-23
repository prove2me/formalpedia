-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.appLE_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:22.625515+00:00
-- url     : https://prove2.me/submissions/7a42f3e1-ffea-4657-b0bb-b9d056e9f0c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat

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
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens} {W : X.Opens}
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl
end ReciprocityTheory.ChartRestriction.G.DVR.TG
