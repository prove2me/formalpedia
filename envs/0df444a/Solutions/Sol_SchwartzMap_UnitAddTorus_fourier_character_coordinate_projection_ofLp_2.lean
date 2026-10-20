-- Prove2me | solution 2 for SchwartzMap.UnitAddTorus.fourier_character_coordinate_projection_ofLp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:47:39.866337+00:00
-- url     : https://prove2.me/submissions/4e7d7e09-fa99-48bb-ad68-4cf5ebcbb1fa

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators Real
open MeasureTheory
open SchwartzMap SchwartzMap.UnitAddTorus


theorem solution (n : ℕ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coordinateTorusProjection n (WithLp.ofLp x)) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  change (∏ i : Fin n, fourier (k i) (((WithLp.ofLp x) i : ℝ) : UnitAddCircle)) = _
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

