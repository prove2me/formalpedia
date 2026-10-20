-- Prove2me | solution 2 for PeriodicConstant.inset_axis_cell_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:02.135478+00:00
-- url     : https://prove2.me/submissions/306e8911-0070-494e-a497-6398002ace06

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
    volume (insetAxisAlignedCell (d := d) L r) = (ENNReal.ofReal (L - 2 * r)) ^ d := by
  have hset : insetAxisAlignedCell (d := d) L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
    ext x
    simp [insetAxisAlignedCell, Set.mem_pi, Pi.le_def, forall_and]
  rw [hset, (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet]
  rw [volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  ring

