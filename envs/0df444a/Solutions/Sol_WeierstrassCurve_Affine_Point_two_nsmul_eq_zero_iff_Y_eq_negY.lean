-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.two_nsmul_eq_zero_iff_Y_eq_negY
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/48cc48ee-14aa-5ebe-a774-edad634ed2d0

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY

open WeierstrassCurve.Affine.Point
theorem solution {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y) :
    2 • (some _ _ h : W.Point) = 0 ↔ y = W.negY x y := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, neg_some]
  exact ⟨fun hP => (some.inj hP).right, fun hy => by simp only [some.injEq]; exact ⟨trivial, hy⟩⟩

end S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY (solution)
