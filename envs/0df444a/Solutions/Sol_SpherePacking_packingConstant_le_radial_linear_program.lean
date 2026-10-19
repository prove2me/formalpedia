-- Prove2me | solution 1 for SpherePacking.packingConstant_le_radial_linear_program
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/201de963-df11-408e-b3c1-bb1ef0fcf1ea

import Theorems.Thm_PackingBounds_PackingBridge_sphere_packing_le_radial_linear_program_ennreal
import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_packingConstant_eq_SpherePackingConstant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal Pointwise
open SpherePacking
namespace SpherePacking
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    packingConstant n ≤ ENNReal.ofReal (CohnElkies.linearProgram n) := by
  rw [packingConstant_eq_SpherePackingConstant]
  exact PackingBounds.PackingBridge.sphere_packing_le_radial_linear_program_ennreal hn
end SpherePacking
