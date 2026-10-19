-- Prove2me | solution 1 for PeriodicConstantApprox.axis_lattice_covolume_toNNReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/385c3bb3-edd2-40c5-8bbc-83468a0b54a7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstantApprox_axis_lattice_covolume_eq_cell_volume

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
open scoped ENNReal
open ZSpan
namespace PeriodicConstantApprox
theorem _root_.solution (L : ℝ) (hL : 0 < L) :
    Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume) =
      (volume (axisAlignedCell (d := d) L)).toNNReal := by
  simp [axis_lattice_covolume_eq_cell_volume (d := d) (L := L) hL]
end PeriodicConstantApprox
