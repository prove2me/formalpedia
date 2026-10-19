-- Prove2me | solution 1 for PeriodicConstantApprox.axis_shell_relative_cell_volume_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/2e8907cb-5c06-4a16-baea-1676cfd47151

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstant_axis_cell_volume_formula
import Theorems.Thm_PeriodicConstantApprox_axis_shell_volume_power_formula
import Theorems.Thm_PeriodicConstantApprox_axis_shell_volume_ratio_tends_zero

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
theorem _root_.solution :
    Tendsto
        (fun L : ℝ =>
          volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
              insetAxisAlignedCell (d := d) L 1) /
            volume (axisAlignedCell (d := d) L))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hlimit : Tendsto
      (fun L : ℝ => ENNReal.ofReal (((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (axis_shell_volume_ratio_tends_zero (d := d))
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hLplus : 0 ≤ L + 1 := by linarith
  have hLminus : 0 ≤ L - 2 := by linarith
  rw [axis_shell_volume_power_formula, PeriodicConstant.axis_cell_volume_formula,
    ← ENNReal.ofReal_pow hLplus d, ← ENNReal.ofReal_pow hLminus d,
    ← ENNReal.ofReal_pow hL0.le d,
    ← ENNReal.ofReal_sub,
    ← ENNReal.ofReal_div_of_pos (pow_pos hL0 d)]
  exact pow_nonneg hLminus d
end PeriodicConstantApprox
