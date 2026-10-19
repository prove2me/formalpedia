-- Prove2me | solution 1 for PeriodicConstantApprox.boundary_half_ball_subset_outer_annulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/1e1fdba8-0d9e-483e-a9e3-e72dddc36aa3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstantApprox_coordinate_abs_lt_of_norm_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open scoped ENNReal Pointwise BigOperators
namespace PeriodicConstantApprox
theorem _root_.solution (L : ℝ) :
    ((axisAlignedCell (d := d) L \ insetAxisAlignedCell (d := d) L (1 / 2)) +
        ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
      ⊆ ((constantCoordinateVector (d := d) (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1 := by
  intro x hx
  rcases hx with ⟨a, ⟨ha, ha_boundary⟩, b, hb, rfl⟩
  have hb_norm : ‖b‖ < (1 / 2 : ℝ) := by
    simpa [mem_ball_zero_iff] using hb
  constructor
  · refine Set.mem_vadd_set.2
      ⟨a + b - constantCoordinateVector (d := d) (-(1 / 2 : ℝ)), ?_, ?_⟩
    · intro i
      rcases ha i with ⟨ha_nonneg, ha_lt⟩
      have hbi := coordinate_abs_lt_of_norm_bound (d := d) hb_norm i
      rcases abs_lt.mp hbi with ⟨hb_lower, hb_upper⟩
      change 0 ≤ (a + b - constantCoordinateVector (d := d) (-(1 / 2 : ℝ))) i ∧
        (a + b - constantCoordinateVector (d := d) (-(1 / 2 : ℝ))) i ≤ L + 1 - 0
      simp only [PiLp.sub_apply, PiLp.add_apply, constantCoordinateVector]
      constructor <;> linarith
    · simp [vadd_eq_add]
  · intro h_inset
    apply ha_boundary
    intro i
    have hxi := h_inset i
    have hbi := coordinate_abs_lt_of_norm_bound (d := d) hb_norm i
    rcases abs_lt.mp hbi with ⟨hb_lower, hb_upper⟩
    change (1 / 2 : ℝ) ≤ a i ∧ a i ≤ L - 1 / 2
    change 1 ≤ (a + b) i ∧ (a + b) i ≤ L - 1 at hxi
    simp only [PiLp.add_apply] at hxi
    rcases hxi with ⟨hx_lower, hx_upper⟩
    constructor <;> linarith
end PeriodicConstantApprox
