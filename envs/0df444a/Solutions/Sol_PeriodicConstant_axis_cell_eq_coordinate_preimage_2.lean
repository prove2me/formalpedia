-- Prove2me | solution 2 for PeriodicConstant.axis_cell_eq_coordinate_preimage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:22:55.282057+00:00
-- url     : https://prove2.me/submissions/b9fc0726-12eb-4be3-8ca2-f48e8be8351a

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
    axisAlignedCell (d := d) L =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
  ext x
  simp [axisAlignedCell, Set.mem_pi]

