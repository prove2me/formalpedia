-- Prove2me | solution 1 for SchwartzMap.UnitAddTorus.fourier_character_coordinate_projection_ofLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/aee6aa4e-e87c-425c-93fd-df8bea225232

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_UnitAddTorus_fourier_character_coordinate_projection

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators Real
open MeasureTheory
open SchwartzMap SchwartzMap.UnitAddTorus
namespace SchwartzMap.UnitAddTorus
theorem _root_.solution (n : ℕ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coordinateTorusProjection n (WithLp.ofLp x)) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simpa using! (fourier_character_coordinate_projection (n := n) (k := k) (x := WithLp.ofLp x))
end SchwartzMap.UnitAddTorus
