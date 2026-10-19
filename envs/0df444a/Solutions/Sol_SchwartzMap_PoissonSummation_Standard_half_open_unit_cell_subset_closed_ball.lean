-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_subset_closed_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/34ab8fad-d76f-4ac2-a2c9-cbea8b042712

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
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution :
    SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d) ⊆
      Metric.closedBall (0 : (EuclideanSpace ℝ (Fin d))) (Real.sqrt d) := by
  intro x hx
  have hsum : (∑ i : Fin d, ‖x i‖ ^ 2) ≤ (d : ℝ) := by
    have hterm : ∀ i : Fin d, ‖x i‖ ^ 2 ≤ (1 : ℝ) := by
      intro i
      have hi : x i ∈ Set.Ioc (0 : ℝ) 1 := hx i
      have hxle : ‖x i‖ ≤ (1 : ℝ) := by
        have hxnonneg : 0 ≤ x i := le_of_lt hi.1
        simpa [Real.norm_eq_abs, abs_of_nonneg hxnonneg] using! hi.2
      simpa [pow_two] using! mul_le_mul hxle hxle (norm_nonneg _) (by positivity)
    simpa using! (Finset.sum_le_sum fun i _ => hterm i).trans_eq (by simp)
  simpa [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq] using! (Real.sqrt_le_sqrt hsum)
end SchwartzMap.PoissonSummation.Standard
