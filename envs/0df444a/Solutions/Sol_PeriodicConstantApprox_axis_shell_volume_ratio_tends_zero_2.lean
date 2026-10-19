-- Prove2me | solution 2 for PeriodicConstantApprox.axis_shell_volume_ratio_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:17:13.848883+00:00
-- url     : https://prove2.me/submissions/6695dd0d-b7b4-4f6c-aea5-d32bde5e7671

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


theorem solution :
    Tendsto (fun L : ℝ => ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)) atTop (𝓝 (0 : ℝ)) := by
  have h1 : Tendsto (fun L : ℝ => (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d) atTop (𝓝 0) := by
    have h0 := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have : Tendsto (fun L : ℝ => (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d) atTop
        (𝓝 ((1 + 0) ^ d - (1 - 2 * 0) ^ d)) :=
      (((tendsto_const_nhds.add h0).pow d).sub ((tendsto_const_nhds.sub (h0.const_mul 2)).pow d))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  rw [sub_div, ← div_pow, ← div_pow]
  congr 2 <;> field_simp <;> ring_nf

