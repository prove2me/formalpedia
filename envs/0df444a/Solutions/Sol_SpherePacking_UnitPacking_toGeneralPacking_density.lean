-- Prove2me | solution 1 for SpherePacking.UnitPacking.toGeneralPacking_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/2c5efa7b-f8dc-41fd-a233-ba13477b130a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_UnitPacking_toGeneralPacking_finiteDensity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal Pointwise
open SpherePacking
namespace SpherePacking
namespace UnitPacking
theorem _root_.solution {n : ℕ} (P : UnitPacking n) :
    P.toGeneralPacking.upperPackingDensity = upperDensity P := by
  unfold _root_.SpherePacking.upperPackingDensity upperDensity
  congr 1
  funext R
  exact P.toGeneralPacking_finiteDensity R
end UnitPacking
end SpherePacking
