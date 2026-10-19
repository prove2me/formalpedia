-- Prove2me | solution 1 for PeriodicConstant.inset_cell_eq_coordinate_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/3363f383-364f-4962-8f54-4e2875540924

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
theorem _root_.solution (L r : ℝ) :
    insetAxisAlignedCell (d := d) L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
  ext x
  simp [insetAxisAlignedCell, Pi.le_def, forall_and]
end PeriodicConstant
