-- Prove2me | solution 1 for SchwartzMap.UnitAddTorus.fourier_character_coordinate_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/ef8a271c-5043-4190-83a9-afb45f656f39

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators Real
open MeasureTheory
open SchwartzMap SchwartzMap.UnitAddTorus
namespace SchwartzMap.UnitAddTorus
theorem _root_.solution (n : ℕ) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (coordinateTorusProjection n x) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simpa [UnitAddTorus.mFourier, ContinuousMap.coe_mk, coordinateTorusProjection, fourier_coe_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using!
    (Complex.exp_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => 2 * π * Complex.I * ((k i : ℝ) * x i))).symm
end SchwartzMap.UnitAddTorus
