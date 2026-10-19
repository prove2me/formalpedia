-- Prove2me | solution 1 for PeriodicConstantApprox.unit_inset_cell_subset_shifted_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/1ea93282-a2fa-4ac7-b7a2-fe731f5b74e1

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
namespace PeriodicConstantApprox
theorem _root_.solution (L : ℝ) :
    insetAxisAlignedCell (d := d) L 1 ⊆
      (uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0 := by
  intro x hx
  refine (Set.mem_vadd_set_iff_neg_vadd_mem).2 ?_
  have hx' : ∀ i : Fin d, x.ofLp i ∈ Set.Icc (1 : ℝ) (L - 1) := by
    simpa [insetAxisAlignedCell, Set.mem_setOf_eq] using! hx
  simp only [insetAxisAlignedCell, Set.mem_setOf_eq, uniformShellShift, vadd_eq_add, one_div, WithLp.ofLp_add,
    WithLp.ofLp_neg, Pi.add_apply, Pi.neg_apply, neg_neg]
  exact fun i => by
    let hxi := hx' i
    refine ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
end PeriodicConstantApprox
