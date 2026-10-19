-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.half_open_unit_cell_volume_finite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:38.684979+00:00
-- url     : https://prove2.me/submissions/8996502c-0f1f-4031-8bae-2d9b3e529120

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
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (SchwartzMap.PoissonSummation.Standard.halfOpenUnitCell (d := d)) < ⊤ := by
  apply Bornology.IsBounded.measure_lt_top
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt d, fun x hx => ?_⟩
  have hx' : ∀ i : Fin d, x i ∈ Set.Ioc (0:ℝ) 1 := hx
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ i : Fin d, (1:ℝ) := Finset.sum_le_sum fun i _ => by
          have := hx' i; rw [Real.norm_eq_abs, sq_abs]; nlinarith [this.1, this.2]
    _ = d := by simp

