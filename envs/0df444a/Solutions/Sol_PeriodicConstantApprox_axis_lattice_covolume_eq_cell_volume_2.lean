-- Prove2me | solution 2 for PeriodicConstantApprox.axis_lattice_covolume_eq_cell_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:21.518252+00:00
-- url     : https://prove2.me/submissions/aa96aefc-fff5-4f1f-9071-f234af56f41a

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
open scoped ENNReal
open ZSpan


theorem solution (L : ℝ) (hL : 0 < L) :
    ZLattice.covolume (axisCellLattice (d := d) L hL) volume =
      (volume (axisAlignedCell (d := d) L)).toReal := by
  letI : DiscreteTopology (axisCellLattice (d := d) L hL) := by
    unfold axisCellLattice; infer_instance
  letI : IsZLattice ℝ (axisCellLattice (d := d) L hL) := by
    unfold axisCellLattice; infer_instance
  have h := ZLattice.covolume_eq_measure_fundamentalDomain (axisCellLattice (d := d) L hL) volume
    (ZSpan.isAddFundamentalDomain (axisCellBasis (d := d) L hL) volume)
  rw [axis_cell_basis_fundamental_region] at h
  rw [h]
  rfl

