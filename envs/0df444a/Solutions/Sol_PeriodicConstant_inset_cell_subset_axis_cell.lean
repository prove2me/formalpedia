-- Prove2me | solution 1 for PeriodicConstant.inset_cell_subset_axis_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/d359caa5-8537-4897-9751-507c3c9dba34

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
theorem _root_.solution {L r : ℝ} (hr : 0 < r) :
    insetAxisAlignedCell (d := d) L r ⊆ axisAlignedCell (d := d) L := by
  intro x hx i
  have hxi := hx i
  exact ⟨(le_of_lt hr).trans hxi.1, hxi.2.trans_lt (sub_lt_self L hr)⟩
end PeriodicConstant
