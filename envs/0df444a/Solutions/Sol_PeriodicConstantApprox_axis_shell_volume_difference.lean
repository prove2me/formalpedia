-- Prove2me | solution 1 for PeriodicConstantApprox.axis_shell_volume_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/883f4ad2-e69f-4b13-9636-60df42eec4b1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstant_inset_cell_eq_coordinate_preimage
import Theorems.Thm_PeriodicConstant_inset_axis_cell_volume_formula
import Theorems.Thm_PeriodicConstantApprox_unit_inset_cell_subset_shifted_shell

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
theorem _root_.solution (L : ℝ) :
    volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1) =
      volume (insetAxisAlignedCell (d := d) (L + 1) 0) - volume (insetAxisAlignedCell (d := d) L 1) := by
  have hsub :
      insetAxisAlignedCell (d := d) L 1 ⊆
        (uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0 :=
    unit_inset_cell_subset_shifted_shell (d := d) L
  have hmeas_inner : MeasurableSet (insetAxisAlignedCell (d := d) L 1) := by
    have hmeasPi :
        MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc (1 : ℝ) (L - 1)) := by
      refine MeasurableSet.pi Set.countable_univ ?_
      intro _ _
      exact measurableSet_Icc
    have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) := by
      simpa using! (PiLp.volume_preserving_ofLp (ι := Fin d))
    simpa [PeriodicConstant.inset_cell_eq_coordinate_preimage (d := d) (L := L) (r := (1 : ℝ))] using!
      hmeasPi.preimage hmp.measurable
  have hfin : volume (insetAxisAlignedCell (d := d) L 1) ≠ ∞ := by
    simp [PeriodicConstant.inset_axis_cell_volume_formula]
  simpa [measure_vadd, uniformShellShift] using!
    (measure_sdiff (μ := volume) hsub hmeas_inner.nullMeasurableSet hfin)
end PeriodicConstantApprox
