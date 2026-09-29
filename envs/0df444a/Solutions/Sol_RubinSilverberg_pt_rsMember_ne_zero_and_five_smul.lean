-- Prove2me | solution 1 for RubinSilverberg.pt_rsMember_ne_zero_and_five_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1a5b1a43-52bd-5f4d-89ca-c10f28761467

import Theorems.Thm_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember
import Theorems.Thm_RubinSilverberg_pt_kleinCurve_ne_zero_and_five_smul
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_pt_rsMember_ne_zero_and_five_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open RubinSilverberg

namespace FrobDictC5

theorem pt_variableChange_eq {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    (C : WeierstrassCurve.VariableChange K) (e : W.toAffine.Point ≃+ (C • W).toAffine.Point)
    (he : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      ∃ h' : (C • W).toAffine.Nonsingular ((↑C.u⁻¹ : K) ^ 2 * (x - C.r))
        ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))),
        e (WeierstrassCurve.Affine.Point.some x y h) =
          WeierstrassCurve.Affine.Point.some ((↑C.u⁻¹ : K) ^ 2 * (x - C.r))
            ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))) h')
    {x y X Y : K} (hns : W.toAffine.Nonsingular x y) (ex : (↑C.u⁻¹ : K) ^ 2 * (x - C.r) = X)
    (ey : (↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t)) = Y) :
    pt (C • W) X Y = e (pt W x y) := by
  obtain ⟨h', hpt⟩ := he x y hns
  subst ex ey
  rw [pt_eq_some hns, hpt, pt_eq_some h']

theorem nonsingular_of_pt_ne_zero {K : Type*} [Field K] {W : WeierstrassCurve K} {x y : K}
    (h : pt W x y ≠ 0) : W.toAffine.Nonsingular x y := by
  by_contra hns
  exact h (pt_eq_zero hns)

end FrobDictC5

open FrobDictC5 in
theorem solution {K : Type*} [Field K] [CharZero K] [DecidableEq K] {a b u₀ : K} (hd : IsKleinDatum a b u₀) (ha : a ≠ 0) (hb : b ≠ 0) (l t k w : K) (hden : rsDen u₀ l t ≠ 0) (hV : kleinV (rsNum u₀ l t / rsDen u₀ l t) ≠ 0) (hk : k ^ 2 = -18 * (b / a) * kleinH u₀ / kleinT u₀) (hw : w ^ 5 = (rsNum u₀ l t / rsDen u₀ l t) ^ 5) : pt (rsMember a b u₀ l t) (k ^ 2 * rsDen u₀ l t ^ 10 * kleinX w) (k ^ 3 * rsDen u₀ l t ^ 15 * kleinY w) ≠ 0 ∧ (5 : ℤ) • pt (rsMember a b u₀ l t) (k ^ 2 * rsDen u₀ l t ^ 10 * kleinX w) (k ^ 3 * rsDen u₀ l t ^ 15 * kleinY w) = 0 := by
  obtain ⟨C, hu, hr, hs, ht, hC⟩ :=
    RubinSilverberg.exists_variableChange_kleinCurve_eq_rsMember hd ha hb l t k hden hk
  rw [← hC]

  have hQ := RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul
    (rsNum u₀ l t / rsDen u₀ l t) w hV hw
  have hns := nonsingular_of_pt_ne_zero hQ.1

  obtain ⟨e, he⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange
    (kleinCurve (rsNum u₀ l t / rsDen u₀ l t)) C
  have ex : (↑C.u⁻¹ : K) ^ 2 * (kleinX w - C.r) = k ^ 2 * rsDen u₀ l t ^ 10 * kleinX w := by
    rw [hu, hr]; ring
  have ey : (↑C.u⁻¹ : K) ^ 3 * (kleinY w - C.s * kleinX w + (C.s * C.r - C.t))
      = k ^ 3 * rsDen u₀ l t ^ 15 * kleinY w := by
    rw [hu, hr, hs, ht]; ring
  rw [pt_variableChange_eq _ C e he hns ex ey]
  exact ⟨(map_ne_zero_iff e e.injective).mpr hQ.1, by rw [← map_zsmul, hQ.2, map_zero]⟩

end S_RubinSilverberg_pt_rsMember_ne_zero_and_five_smul
end P2MW
export P2MW.S_RubinSilverberg_pt_rsMember_ne_zero_and_five_smul (solution)
