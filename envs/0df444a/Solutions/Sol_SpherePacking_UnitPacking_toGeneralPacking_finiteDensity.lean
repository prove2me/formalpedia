-- Prove2me | solution 1 for SpherePacking.UnitPacking.toGeneralPacking_finiteDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/4f0f2b8f-10df-437a-b044-3276eec251ea

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_UnitPacking_covered_eq_toGeneralPacking_balls

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal Pointwise
open SpherePacking
namespace SpherePacking
namespace UnitPacking
theorem _root_.solution {n : ℕ}
    (P : UnitPacking n) (R : ℝ) :
    P.toGeneralPacking.densityInsideRadius R = unitFiniteDensity P R := by
  rw [_root_.SpherePacking.densityInsideRadius, unitFiniteDensity,
    ← P.covered_eq_toGeneralPacking_balls]
end UnitPacking
end SpherePacking
