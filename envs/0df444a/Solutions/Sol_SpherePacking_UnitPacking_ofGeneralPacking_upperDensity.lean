-- Prove2me | solution 1 for SpherePacking.UnitPacking.ofGeneralPacking_upperDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/4ddb17d8-4788-47cd-87b8-1d703c33c9a4

import Theorems.Thm_SpherePacking_rescale_upper_packing_density
import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_UnitPacking_toGeneralPacking_density
import Theorems.Thm_SpherePacking_UnitPacking_toGeneralPacking_ofGeneralPacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal Pointwise
open SpherePacking
namespace SpherePacking
namespace UnitPacking
theorem _root_.solution {n : ℕ}
    (S : _root_.SpherePacking n) :
    upperDensity (UnitPacking.ofGeneralPacking S) = S.upperPackingDensity := by
  rw [← UnitPacking.toGeneralPacking_density,
    UnitPacking.toGeneralPacking_ofGeneralPacking,
    _root_.SpherePacking.rescale_upper_packing_density]
end UnitPacking
end SpherePacking
