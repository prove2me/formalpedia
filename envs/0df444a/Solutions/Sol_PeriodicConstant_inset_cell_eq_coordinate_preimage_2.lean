-- Prove2me | solution 2 for PeriodicConstant.inset_cell_eq_coordinate_preimage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:16.379812+00:00
-- url     : https://prove2.me/submissions/e4f71f7d-04ec-4e78-a47a-c7e9785516c0

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


theorem solution (L r : ℝ) :
    insetAxisAlignedCell (d := d) L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
  ext x
  simp [insetAxisAlignedCell, Set.mem_pi, Pi.le_def, forall_and]

