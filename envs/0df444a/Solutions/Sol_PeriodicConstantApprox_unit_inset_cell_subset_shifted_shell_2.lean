-- Prove2me | solution 2 for PeriodicConstantApprox.unit_inset_cell_subset_shifted_shell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:24.821083+00:00
-- url     : https://prove2.me/submissions/e795820e-c39f-47cd-b0f4-2080e36528c5

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


theorem solution (L : ℝ) :
    insetAxisAlignedCell (d := d) L 1 ⊆
      (uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0 := by
  intro x hx
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  intro i
  have h := hx i
  simp only [Set.mem_Icc] at h ⊢
  simp [uniformShellShift]
  constructor <;> linarith [h.1, h.2]

