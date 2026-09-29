-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.finite_of_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1446a2ba-c53e-5b55-bf5c-6d0e789ab48d

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finite.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_finite_of_finite_field

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

private def twfPointToPair {F : Type*} [Field F] (W : Affine F) :
    W.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

private theorem twfPointToPair_injective {F : Type*} [Field F] (W : Affine F) :
    Function.Injective (twfPointToPair W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [twfPointToPair] at h
  · simp [twfPointToPair] at h
  · simp only [twfPointToPair, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem solution
    {F : Type*} [Field F] [DecidableEq F] [Finite F] (W : Affine F) :
    Finite W.Point :=
  Finite.of_injective (twfPointToPair W) (twfPointToPair_injective W)

end S_WeierstrassCurve_Affine_Point_finite_of_finite_field
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_finite_of_finite_field (solution)
