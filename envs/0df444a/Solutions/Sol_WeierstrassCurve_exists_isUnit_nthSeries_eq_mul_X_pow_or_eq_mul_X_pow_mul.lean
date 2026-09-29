-- Prove2me | solution 1 for WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_pow_or_eq_mul_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6136ef16-8934-52bb-bb1f-e86e554c9242

import Mathlib
import Theorems.Thm_FormalGroup_nthSeries_eq_zero_or_exists_eq_mul_X_pow_pow
import Theorems.Thm_WeierstrassCurve_nthSeries_ne_zero_and_not_X_pow_dvd_of_charP
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_pow_or_eq_mul_X_pow_mul
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open FormalGroup

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (F : FormalGroup k) (hF : F.toPowerSeries = W.formalGroupLawFixed) :
    ∃ u : PowerSeries k, IsUnit u ∧
      (F.nthSeries q = u * PowerSeries.X ^ q ∨ F.nthSeries q = u * PowerSeries.X ^ (q * q)) := by
  classical
  haveI : F.IsComm := ⟨by
    show F.toPowerSeries = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] F.toPowerSeries
    rw [hF]; exact (W.formalGroupLawFixed_comm).symm⟩
  obtain ⟨hne, hndvd⟩ := WeierstrassCurve.nthSeries_ne_zero_and_not_X_pow_dvd_of_charP q k W F hF
  rcases FormalGroup.nthSeries_eq_zero_or_exists_eq_mul_X_pow_pow q k F with hz | ⟨h, u, hh, hu, he⟩
  · exact absurd hz hne
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hle : q ^ h ≤ q * q := by
    by_contra hlt
    apply hndvd
    rw [he]
    exact Dvd.dvd.mul_left (pow_dvd_pow PowerSeries.X (by omega)) u
  have h12 : h = 1 ∨ h = 2 := by
    rcases h with _ | _ | _ | h
    · omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have h3 : q ^ 3 ≤ q ^ (h + 1 + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3' : q ^ 3 = q * q * q := by ring
      have hqq : q * q < q * q * q := by nlinarith
      omega
  refine ⟨u, hu, ?_⟩
  rcases h12 with rfl | rfl
  · left; rw [he, pow_one]
  · right; rw [he, pow_two]

end S_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_pow_or_eq_mul_X_pow_mul
end P2MW
export P2MW.S_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_pow_or_eq_mul_X_pow_mul (solution)
