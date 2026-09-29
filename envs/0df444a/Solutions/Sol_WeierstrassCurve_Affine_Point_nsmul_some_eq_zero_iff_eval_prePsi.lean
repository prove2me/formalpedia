-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/71ccef51-674e-58ab-9756-33ee567419b2

import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Polynomial
open scoped Polynomial.Bivariate

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : Odd n) {x y : F} (h : W.toAffine.Nonsingular x y) :
    n • Point.some x y h = 0 ↔ (W.preΨ' n).eval x = 0 := by
  rw [← natCast_zsmul, WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h (n : ℤ)]

  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (Affine.CoordinateRing.mk_ψ W (n : ℤ))
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h.1
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero] at h1
  rw [h1, Ψ_ofNat, if_neg (Nat.not_even_iff_odd.mpr hn), mul_one, evalEval_C]

end S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi (solution)
