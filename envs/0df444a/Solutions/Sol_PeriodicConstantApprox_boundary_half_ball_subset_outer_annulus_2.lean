-- Prove2me | solution 2 for PeriodicConstantApprox.boundary_half_ball_subset_outer_annulus
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:50:39.54499+00:00
-- url     : https://prove2.me/submissions/4216324d-5097-4fcb-ab6a-ce9a25b6c794

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
open scoped ENNReal Pointwise BigOperators


theorem solution (L : ℝ) :
    ((axisAlignedCell (d := d) L \ insetAxisAlignedCell (d := d) L (1 / 2)) +
        ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
      ⊆ ((constantCoordinateVector (d := d) (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
        insetAxisAlignedCell (d := d) L 1 := by
  rintro z ⟨y, ⟨hy, hyn⟩, w, hw, rfl⟩
  simp only [axisAlignedCell, insetAxisAlignedCell, Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Icc] at hy hyn
  push_neg at hyn
  have hwi : ∀ i, |w i| < 1 / 2 := fun i =>
    lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w i) (mem_ball_zero_iff.mp hw)
  constructor
  · refine ⟨(y + w) - constantCoordinateVector (d := d) (-(1 / 2 : ℝ)), ?_, ?_⟩
    · intro i
      have h1 := abs_lt.mp (hwi i)
      have h2 := hy i
      simp only [constantCoordinateVector, PiLp.sub_apply, PiLp.add_apply, Set.mem_Icc]
      constructor <;> simp <;> linarith
    · simp [vadd_eq_add]
  · intro hcon
    simp only [insetAxisAlignedCell, Set.mem_setOf_eq, Set.mem_Icc] at hcon
    obtain ⟨i, hi⟩ := hyn
    have h1 := abs_lt.mp (hwi i)
    have h3 := hcon i
    simp only [PiLp.add_apply] at h3
    by_cases hlt : 1 / 2 ≤ y i
    · have := hi hlt; linarith [h3.2]
    · push_neg at hlt; linarith [h3.1]

