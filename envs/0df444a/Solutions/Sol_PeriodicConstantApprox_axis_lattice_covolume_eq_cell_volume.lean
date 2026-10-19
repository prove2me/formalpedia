-- Prove2me | solution 1 for PeriodicConstantApprox.axis_lattice_covolume_eq_cell_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/8a4854d8-469a-4aa2-8479-1516044490eb

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
namespace PeriodicConstantApprox
theorem _root_.solution (L : ℝ) (hL : 0 < L) :
    ZLattice.covolume (axisCellLattice (d := d) L hL) volume =
      (volume (axisAlignedCell (d := d) L)).toReal := by
  letI : DiscreteTopology (axisCellLattice (d := d) L hL) :=
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
      (axisCellBasis (d := d) L hL)
  letI : IsZLattice ℝ (axisCellLattice (d := d) L hL) :=
    instIsZLatticeRealSpan (axisCellBasis (d := d) L hL)
  have hfund :
      IsAddFundamentalDomain (axisCellLattice (d := d) L hL)
        (fundamentalDomain (axisCellBasis (d := d) L hL)) volume := by
    simpa [axisCellLattice] using! (ZSpan.isAddFundamentalDomain (axisCellBasis (d := d) L hL) volume)
  simpa [Measure.real, axis_cell_basis_fundamental_region (d := d) (L := L) (hL := hL)] using!
    (ZLattice.covolume_eq_measure_fundamentalDomain (L := axisCellLattice (d := d) L hL)
      (μ := volume) hfund)
end PeriodicConstantApprox
