-- Prove2me | solution 1 for RubinSilverberg.rsMember_sections_independent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7d8ba23e-6b1a-53c1-9713-ec3a5b2a91d8

import Theorems.Thm_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember
import Theorems.Thm_RubinSilverberg_pt_kleinCurve_ne_zero_and_five_smul
import Theorems.Thm_RubinSilverberg_kleinSection_independent
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_rsMember_sections_independent
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
theorem solution {K : Type*} [Field K] [CharZero K] [DecidableEq K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) {a b u₀ : K} (hd : IsKleinDatum a b u₀) (ha : a ≠ 0) (hb : b ≠ 0) (l t k : K) (hden : rsDen u₀ l t ≠ 0) (hV : kleinV (rsNum u₀ l t / rsDen u₀ l t) ≠ 0) (hk : k ^ 2 = -18 * (b / a) * kleinH u₀ / kleinT u₀) (i j : ℤ) (h : i • pt (rsMember a b u₀ l t) (k ^ 2 * rsDen u₀ l t ^ 10 * kleinX (rsNum u₀ l t / rsDen u₀ l t)) (k ^ 3 * rsDen u₀ l t ^ 15 * kleinY (rsNum u₀ l t / rsDen u₀ l t)) + j • pt (rsMember a b u₀ l t) (k ^ 2 * rsDen u₀ l t ^ 10 * kleinX (ζ * (rsNum u₀ l t / rsDen u₀ l t))) (k ^ 3 * rsDen u₀ l t ^ 15 * kleinY (ζ * (rsNum u₀ l t / rsDen u₀ l t))) = 0) : (5 : ℤ) ∣ i ∧ (5 : ℤ) ∣ j := by
  obtain ⟨C, hu, hr, hs, ht, hC⟩ :=
    RubinSilverberg.exists_variableChange_kleinCurve_eq_rsMember hd ha hb l t k hden hk
  rw [← hC] at h

  have hζv : (ζ * (rsNum u₀ l t / rsDen u₀ l t)) ^ 5 = (rsNum u₀ l t / rsDen u₀ l t) ^ 5 := by
    rw [mul_pow, hζ.pow_eq_one, one_mul]

  have hns₁ := nonsingular_of_pt_ne_zero (RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul
    (rsNum u₀ l t / rsDen u₀ l t) (rsNum u₀ l t / rsDen u₀ l t) hV rfl).1
  have hns₂ := nonsingular_of_pt_ne_zero (RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul
    (rsNum u₀ l t / rsDen u₀ l t) (ζ * (rsNum u₀ l t / rsDen u₀ l t)) hV hζv).1

  obtain ⟨e, he⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange
    (kleinCurve (rsNum u₀ l t / rsDen u₀ l t)) C
  have ex : ∀ w : K, (↑C.u⁻¹ : K) ^ 2 * (kleinX w - C.r) = k ^ 2 * rsDen u₀ l t ^ 10 * kleinX w := by
    intro w; rw [hu, hr]; ring
  have ey : ∀ w : K, (↑C.u⁻¹ : K) ^ 3 * (kleinY w - C.s * kleinX w + (C.s * C.r - C.t))
      = k ^ 3 * rsDen u₀ l t ^ 15 * kleinY w := by
    intro w; rw [hu, hr, hs, ht]; ring
  rw [pt_variableChange_eq _ C e he hns₁ (ex _) (ey _),
    pt_variableChange_eq _ C e he hns₂ (ex _) (ey _), ← map_zsmul, ← map_zsmul, ← map_add,
    map_eq_zero_iff e e.injective] at h
  exact RubinSilverberg.kleinSection_independent ζ hζ (rsNum u₀ l t / rsDen u₀ l t) hV i j h

end S_RubinSilverberg_rsMember_sections_independent
end P2MW
export P2MW.S_RubinSilverberg_rsMember_sections_independent (solution)
