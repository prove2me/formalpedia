-- Prove2me | solution 2 for PeriodicConstant.axis_cell_is_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:17:53.791935+00:00
-- url     : https://prove2.me/submissions/0e79e224-dc4c-4e01-aca0-97a5c37af59d

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


theorem solution (L : ℝ) (hL : 0 < L) :
    MeasurableSet (axisAlignedCell (d := d) L) := by
  have : axisAlignedCell (d := d) L = ⋂ i : Fin d, (fun x : EuclideanSpace ℝ (Fin d) => x i) ⁻¹' Set.Ico 0 L := by
    ext x; simp [axisAlignedCell]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_Ico.preimage
    ((by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin d) => x i).measurable)

