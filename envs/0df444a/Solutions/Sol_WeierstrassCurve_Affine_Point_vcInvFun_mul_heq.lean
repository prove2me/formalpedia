-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.vcInvFun_mul_heq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b9faf677-ad93-55a4-9026-36104efa42c0

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace VCMulGlue

theorem heq_some_of_eq {K : Type*} [Field K] {V V' : WeierstrassCurve.Affine K} (hV : V = V') {x y x' y' : K}
    (hx : x = x') (hy : y = y') (h : V.Nonsingular x y) (h' : V'.Nonsingular x' y') :
    HEq (Point.some x y h) (Point.some x' y' h') := by
  subst hV hx hy
  rfl

theorem heq_zero_of_eq {K : Type*} [Field K] {V V' : WeierstrassCurve.Affine K} (hV : V = V') :
    HEq (0 : V.Point) (0 : V'.Point) := by
  subst hV
  rfl

theorem vcXInv_mul {K : Type*} [Field K] (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  simp only [vcXInv, VariableChange.mul_def, Units.val_mul, Units.val_inv_eq_inv_val]
  have hu : ((C.u : K)) ≠ 0 := C.u.ne_zero
  have hu' : ((C'.u : K)) ≠ 0 := C'.u.ne_zero
  field_simp
  ring

theorem vcYInv_mul {K : Type*} [Field K] (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  simp only [vcYInv, vcXInv, VariableChange.mul_def, Units.val_mul, Units.val_inv_eq_inv_val]
  have hu : ((C.u : K)) ≠ 0 := C.u.ne_zero
  have hu' : ((C'.u : K)) ≠ 0 := C'.u.ne_zero
  field_simp
  ring

end VCMulGlue

open VCMulGlue in
theorem solution
    {K : Type*} [Field K] [DecidableEq K]
    (C C' : VariableChange K) (W : WeierstrassCurve.Affine K) (T : W.Point) :
    HEq (Point.vcInvFun (C * C') W T) (Point.vcInvFun C (C' • W) (Point.vcInvFun C' W T)) := by
  have hW : (C * C') • W = C • C' • W := mul_smul C C' W
  rcases T with _ | ⟨x, y, h⟩
  · exact heq_zero_of_eq hW
  · simp only [Point.vcInvFun]
    exact heq_some_of_eq hW (vcXInv_mul C C' x) (vcYInv_mul C C' x y) _ _

end S_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_mul_heq (solution)
