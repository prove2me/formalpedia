-- Prove2me | solution 2 for PeriodicConstant.axis_cell_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:00:10.804018+00:00
-- url     : https://prove2.me/submissions/690d1db6-5b05-4abc-9f09-01d7288bdc63

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
open PeriodicConstant
variable {d : ℕ}


theorem solution (L : ℝ) :
    volume (axisAlignedCell (d := d) L) = (ENNReal.ofReal L) ^ d := by
  have hset : axisAlignedCell (d := d) L =
      (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) L) := by
    ext x; simp [axisAlignedCell]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ico)).nullMeasurableSet, Real.volume_pi_Ico]
  simp

