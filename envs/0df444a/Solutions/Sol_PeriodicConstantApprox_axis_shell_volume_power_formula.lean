-- Prove2me | solution 1 for PeriodicConstantApprox.axis_shell_volume_power_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/a03859c8-31b2-488a-a3f1-89cb967e31cb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstant_inset_axis_cell_volume_formula
import Theorems.Thm_PeriodicConstantApprox_axis_shell_volume_difference

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open Filter
variable {d : ℕ}
namespace PeriodicConstantApprox
theorem _root_.solution (L : ℝ) :
    volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1) =
      (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d := by
  rw [axis_shell_volume_difference (d := d) (L := L)]
  simp [PeriodicConstant.inset_axis_cell_volume_formula]
end PeriodicConstantApprox
