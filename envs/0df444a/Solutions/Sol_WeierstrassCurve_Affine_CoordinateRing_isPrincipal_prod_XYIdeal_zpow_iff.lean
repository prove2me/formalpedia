-- Prove2me | solution 1 for WeierstrassCurve.Affine.CoordinateRing.isPrincipal_prod_XYIdeal_zpow_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3ad29414-b8b3-5ea6-b1c8-eee65a2dade7

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff

open WeierstrassCurve WeierstrassCurve.Affine
open scoped nonZeroDivisors

theorem solution {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {ι : Type*} (s : Finset ι) (x y : ι → F) (h : ∀ i, W.toAffine.Nonsingular (x i) (y i)) (m : ι → ℤ) : ((∏ i ∈ s, CoordinateRing.XYIdeal' (h i) ^ m i : (FractionalIdeal W.toAffine.CoordinateRing⁰ W.toAffine.FunctionField)ˣ) : Submodule W.toAffine.CoordinateRing W.toAffine.FunctionField).IsPrincipal ↔ ∑ i ∈ s, m i • Point.some (x i) (y i) (h i) = 0 := by
  rw [← ClassGroup.mk_eq_one_iff, ← Point.toClass_eq_zero, map_sum]
  have key : Additive.toMul (∑ i ∈ s, Point.toClass (m i • Point.some (x i) (y i) (h i))) =
      ClassGroup.mk W.toAffine.FunctionField (∏ i ∈ s, CoordinateRing.XYIdeal' (h i) ^ m i) := by
    rw [map_prod, toMul_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zsmul, toMul_zsmul, map_zpow, Point.toClass_some]
    rfl
  rw [← key]
  exact Additive.toMul.apply_eq_iff_eq_symm_apply

end S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff
end P2MW
export P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff (solution)
