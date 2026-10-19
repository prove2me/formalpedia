-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.fourier_character_euclidean_projection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:10.630688+00:00
-- url     : https://prove2.me/submissions/618f3a31-a7a2-4951-a0b5-3d2ac9e7f73f

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


theorem solution (n : Fin d → ℤ) (x : (EuclideanSpace ℝ (Fin d))) :
    UnitAddTorus.mFourier n (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      (𝐞 (inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) : ℂ) := by
  have h : UnitAddTorus.mFourier n (euclideanTorusProjection x) =
      ∏ i, Complex.exp (2 * Real.pi * Complex.I * (n i) * (x i) / (1:ℝ)) := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, euclideanTorusProjection,
      SchwartzMap.UnitAddTorus.coordinateTorusProjection]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact fourier_coe_apply
  rw [h, ← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  rw [PiLp.inner_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [embeddedIntegerVector]
  ring

