-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_subset_closed_ball
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:29:04.734631+00:00
-- url     : https://prove2.me/submissions/7cabb1f5-0ddc-40d5-80ee-7f1950e512bc

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform
open MeasureTheory
open SchwartzMap SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))


theorem solution :
    SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d) ⊆
      Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
        obtain ⟨h1, h2⟩ := hx i
        rw [Real.norm_eq_abs, sq_abs]; nlinarith)
    _ = d := by simp

