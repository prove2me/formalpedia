-- Prove2me | solution 2 for PeriodicConstantApprox.ball_subset_translated_cell_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:30:34.347413+00:00
-- url     : https://prove2.me/submissions/3d920380-f0c6-4b75-b1e5-10b20d07b3eb

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
open scoped Pointwise
open MeasureTheory Metric
open PeriodicConstantApprox
variable {d : ℕ}


theorem solution {L r : ℝ} (hL : 0 < L)
    {v : axisCellLattice (d := d) L hL} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ v +ᵥ insetAxisAlignedCell (d := d) L r) :
    ball x r ⊆ v +ᵥ axisAlignedCell (d := d) L := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hx
  have hzr : ‖z - (v +ᵥ y)‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  refine ⟨z - (v : EuclideanSpace ℝ (Fin d)), ?_, by simp [Submodule.vadd_def]⟩
  intro i
  have hc : ‖(z - (v +ᵥ y)) i‖ ≤ ‖z - (v +ᵥ y)‖ := PiLp.norm_apply_le _ i
  have e1 : (z - (v +ᵥ y)) i = z i - (v : EuclideanSpace ℝ (Fin d)) i - y i := by
    simp [Submodule.vadd_def]; ring
  have e2 : (z - (v : EuclideanSpace ℝ (Fin d))) i = z i - (v : EuclideanSpace ℝ (Fin d)) i := by simp
  rw [e1, Real.norm_eq_abs] at hc
  obtain ⟨h1, h2⟩ := hy i
  have := abs_lt.mp (lt_of_le_of_lt hc hzr)
  rw [Set.mem_Ico, e2]
  constructor <;> linarith [this.1, this.2]

