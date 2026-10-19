-- Prove2me | solution 1 for PeriodicConstantApprox.axis_shell_volume_ratio_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/8a4f81db-e2cb-45b0-a5a3-f4c47d47d286

import Mathlib
import Definitions.Def_SpherePacking

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
    Tendsto (fun L : ℝ => ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)) atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hplus : Tendsto (fun L : ℝ => 1 + L⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hinv)
  have hminus : Tendsto (fun L : ℝ => 1 - 2 * L⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv))
  have hlimit : Tendsto (fun L : ℝ => (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (hplus.pow d).sub (hminus.pow d)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hplus_eq : 1 + L⁻¹ = (L + 1) / L := by
    field_simp [hL.ne']
  have hminus_eq : 1 - 2 * L⁻¹ = (L - 2) / L := by
    field_simp [hL.ne']
  rw [hplus_eq, hminus_eq, div_pow, div_pow, ← sub_div]
end PeriodicConstantApprox
