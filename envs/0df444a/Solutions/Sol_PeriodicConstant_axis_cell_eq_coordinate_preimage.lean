-- Prove2me | solution 1 for PeriodicConstant.axis_cell_eq_coordinate_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/c6aec549-a78f-4f86-9f15-ddaa79abc43b

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
namespace PeriodicConstant
theorem _root_.solution (L : ℝ) :
    axisAlignedCell (d := d) L =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
  ext x
  simp [axisAlignedCell, Set.mem_pi]
end PeriodicConstant
