-- Prove2me | solution 1 for SpherePacking.UnitPacking.covered_eq_toGeneralPacking_balls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/dc6cd4a5-ff97-41ed-bbe8-a4a3fb0d737b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal Pointwise
open SpherePacking
namespace SpherePacking
namespace UnitPacking
theorem _root_.solution {n : ℕ}
    (P : UnitPacking n) :
    covered P = P.toGeneralPacking.occupiedBallRegion := by
  ext x
  simp [covered, _root_.SpherePacking.occupiedBallRegion, UnitPacking.toGeneralPacking]
end UnitPacking
end SpherePacking
