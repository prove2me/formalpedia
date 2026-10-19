-- Prove2me | solution 1 for SpherePacking.rescale_upper_packing_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/872e95ba-7f55-4e9b-a41a-170c1bd2c950

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open MeasureTheory Metric Filter
open Module
open scoped BigOperators ENNReal Pointwise
open SpherePacking
namespace SpherePacking
theorem _root_.solution {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (S.rescaleConfiguration hc).upperPackingDensity = S.upperPackingDensity := by
  simpa [upperPackingDensity, Function.comp, map_div_atTop_eq c hc] using!
    (limsup_congr (Eventually.of_forall fun R => rescale_local_packing_density_radius (S := S) hc R)).trans
      (Filter.limsup_comp (u := S.densityInsideRadius) (v := fun R => R / c) (f := atTop))
end SpherePacking
