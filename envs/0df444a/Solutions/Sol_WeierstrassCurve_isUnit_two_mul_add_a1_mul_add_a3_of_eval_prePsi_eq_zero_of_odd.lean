-- Prove2me | solution 1 for WeierstrassCurve.isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6c88d563-531d-5956-ad20-7c6d6645deb4

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ preΨ_ofNat a₁ map mk preΨ Affine.Point.some preΨ' toAffine Affine.Point ψ₂ map_Δ map_a₁ map_preΨ Affine.Point.some_ne_zero Δ Affine.Point.neg_some map_a₃ Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi"
namespace Psi2Unit
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd.WeierstrassCurve"

variable {T : Type*} [CommRing T]

theorem psi2_ne_zero_field {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    {ℓ : ℕ} (hℓ : Odd ℓ) {x y : k} (heq : W.toAffine.Equation x y) (hψ : (W.preΨ' ℓ).eval x = 0) :
    2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
  intro h0
  have hns : W.toAffine.Nonsingular x y := W.toAffine.equation_iff_nonsingular.mp heq
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hns with hP
  have hℓP : ℓ • P = 0 :=
    (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hℓ hns).mpr hψ
  have hneg : -P = P := by
    rw [hP, WeierstrassCurve.Affine.Point.neg_some]
    congr 1
    show -y - W.a₁ * x - W.a₃ = y
    linear_combination (-1 : k) * h0
  have h2P : 2 • P = 0 := by
    rw [two_nsmul]
    nth_rewrite 2 [← hneg]
    exact add_neg_cancel P
  have hd : addOrderOf P ∣ Nat.gcd ℓ 2 :=
    Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hℓP) (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2P)
  have hg : Nat.gcd ℓ 2 = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hℓ)
  rw [hg, Nat.dvd_one] at hd
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns (AddMonoid.addOrderOf_eq_one_iff.mp hd)

theorem isUnit_psi2 {ℓ : ℕ} (hℓ : Odd ℓ) (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    {x y : T} (heq : W.toAffine.Equation x y) (hψ : (W.preΨ ℓ).eval x = 0) :
    IsUnit (2 * y + W.a₁ * x + W.a₃) := by
  classical
  by_contra hnu
  have hne : Ideal.span ({2 * y + W.a₁ * x + W.a₃} : Set T) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hnu
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : 2 * y + W.a₁ * x + W.a₃ ∈ m := hle (Ideal.mem_span_singleton_self _)
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  set π : T →+* T ⧸ m := Ideal.Quotient.mk m with hπ
  haveI : (W.map π).IsElliptic := by
    refine ⟨?_⟩
    rw [WeierstrassCurve.map_Δ]
    exact hΔ.map π
  have heq' : (W.map π).toAffine.Equation (π x) (π y) := heq.map π
  have hψ' : ((W.map π).preΨ' ℓ).eval (π x) = 0 := by
    rw [← WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hψ, map_zero]
  have h := psi2_ne_zero_field (W.map π) hℓ heq' hψ'
  apply h
  have : π (2 * y + W.a₁ * x + W.a₃) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simp [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at this
  exact this

end WeierstrassCurve.Psi2Unit

theorem solution
    {T : Type*} [CommRing T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    {ℓ : ℕ} (hℓ : Odd ℓ) {x y : T} (heq : W.toAffine.Equation x y) (hℓx : (W.preΨ ℓ).eval x = 0) :
    IsUnit (2 * y + W.a₁ * x + W.a₃) :=
  WeierstrassCurve.Psi2Unit.isUnit_psi2 hℓ W hΔ heq hℓx

end S_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd
end P2MW
export P2MW.S_WeierstrassCurve_isUnit_two_mul_add_a1_mul_add_a3_of_eval_prePsi_eq_zero_of_odd (solution)
