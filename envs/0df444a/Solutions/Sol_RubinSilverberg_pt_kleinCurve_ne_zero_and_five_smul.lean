-- Prove2me | solution 1 for RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/558d3e5d-ba87-5c62-a9b7-91ad38965b7f

import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_RubinSilverberg_kleinCurve_prePsi_five_eval_kleinX
import Theorems.Thm_RubinSilverberg_kleinY_sq
import Theorems.Thm_RubinSilverberg_kleinCurve_Delta
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_pt_kleinCurve_ne_zero_and_five_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "Polynomial WeierstrassCurve~cusp WeierstrassCurve.Affine WeierstrassCurve.Affine.Point RubinSilverberg"

open scoped Polynomial.Bivariate

namespace M4cP4RS

section Section

variable {K : Type*} [Field K]

theorem kleinH_eq_of_pow_five_eq {u w : K} (hw : w ^ 5 = u ^ 5) : kleinH w = kleinH u := by
  have e : ∀ v : K, kleinH v = (v ^ 5) ^ 4 - 228 * (v ^ 5) ^ 3 + 494 * (v ^ 5) ^ 2 + 228 * v ^ 5 + 1 :=
    fun v => by unfold kleinH; ring
  rw [e, e, hw]

theorem kleinT_eq_of_pow_five_eq {u w : K} (hw : w ^ 5 = u ^ 5) : kleinT w = kleinT u := by
  have e : ∀ v : K, kleinT v = (v ^ 5) ^ 6 + 522 * (v ^ 5) ^ 5 - 10005 * (v ^ 5) ^ 4
      - 10005 * (v ^ 5) ^ 2 - 522 * v ^ 5 + 1 := fun v => by unfold kleinT; ring
  rw [e, e, hw]

theorem kleinCurve_eq_of_pow_five_eq {u w : K} (hw : w ^ 5 = u ^ 5) : kleinCurve w = kleinCurve u := by
  simp only [kleinCurve, kleinH_eq_of_pow_five_eq hw, kleinT_eq_of_pow_five_eq hw]

theorem kleinCurve_equation [CharZero K] (u : K) :
    (kleinCurve u).toAffine.Equation (kleinX u) (kleinY u) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show kleinY u ^ 2 + 0 * kleinX u * kleinY u + 0 * kleinY u
      = kleinX u ^ 3 + 0 * kleinX u ^ 2 + (-kleinH u / 48) * kleinX u + kleinT u / 864
  rw [RubinSilverberg.kleinY_sq u]
  ring

theorem evalEval_eq_of_mk_eq (W : WeierstrassCurve K) {p p' : K[X][Y]}
    (hmk : Affine.CoordinateRing.mk W p = Affine.CoordinateRing.mk W p') {x y : K}
    (h : W.toAffine.Equation x y) : p.evalEval x y = p'.evalEval x y := by
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : W.toAffine.polynomial.evalEval x y = 0 := h
  have h1 : (p - p').evalEval x y = 0 := by
    rw [hr, evalEval_mul, h0, zero_mul]
  rwa [evalEval_sub, sub_eq_zero] at h1

theorem evalEval_ψ_five (W : WeierstrassCurve K) {x y : K} (h : W.toAffine.Equation x y) :
    (W.ψ 5).evalEval x y = (W.preΨ' 5).eval x := by
  have h1 := evalEval_eq_of_mk_eq W (Affine.CoordinateRing.mk_ψ (W := W) 5) h
  rw [h1]
  have h5 : W.Ψ 5 = C (W.preΨ' 5) := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by rfl, Ψ_ofNat, if_neg (by decide), mul_one]
  rw [h5, evalEval_C]

theorem main [CharZero K] [DecidableEq K] (u w : K) (hV : kleinV u ≠ 0) (hw : w ^ 5 = u ^ 5) :
    pt (kleinCurve u) (kleinX w) (kleinY w) ≠ 0 ∧ (5 : ℤ) • pt (kleinCurve u) (kleinX w) (kleinY w) = 0 := by
  have hc : kleinCurve u = kleinCurve w := (kleinCurve_eq_of_pow_five_eq hw).symm
  have hΔ : (kleinCurve u).Δ ≠ 0 := by
    rw [RubinSilverberg.kleinCurve_Delta u]
    exact neg_ne_zero.mpr (pow_ne_zero 5 hV)
  have heq : (kleinCurve u).toAffine.Equation (kleinX w) (kleinY w) := by
    rw [hc]
    exact kleinCurve_equation w
  have hns : (kleinCurve u).toAffine.Nonsingular (kleinX w) (kleinY w) :=
    ((kleinCurve u).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp heq
  rw [pt_eq_some hns]
  refine ⟨Point.some_ne_zero hns, ?_⟩
  refine (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (kleinCurve u) hns 5).mpr ?_
  rw [evalEval_ψ_five _ heq, hc]
  exact RubinSilverberg.kleinCurve_prePsi_five_eval_kleinX w

end Section

end M4cP4RS

theorem solution {K : Type*} [Field K] [CharZero K] [DecidableEq K] (u w : K) (hV : kleinV u ≠ 0)
    (hw : w ^ 5 = u ^ 5) :
    pt (kleinCurve u) (kleinX w) (kleinY w) ≠ 0 ∧ (5 : ℤ) • pt (kleinCurve u) (kleinX w) (kleinY w) = 0 :=
  M4cP4RS.main u w hV hw

end S_RubinSilverberg_pt_kleinCurve_ne_zero_and_five_smul
end P2MW
export P2MW.S_RubinSilverberg_pt_kleinCurve_ne_zero_and_five_smul (solution)
