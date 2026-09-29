-- Prove2me | solution 1 for WeierstrassCurve.apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/af95f9ac-990d-53e1-bf73-05fb7807b9f4

import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
      (W.map (Int.castRingHom ℚ)) p σ = 1)
    (μ : AlgebraicClosure ℚ) (hμ : μ ^ p = 1) : σ μ = μ := by
  have hp : p.Prime := Fact.out
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact isUnit_iff_ne_zero.mpr (by simpa using hΔ)⟩
  have hpK : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 := (W.map (Int.castRingHom ℚ)).apply_eq_pow_det_galoisRep_of_pow_eq_one hp hpK σ μ hμ
  have h2 : (DistribSMul.toAddMonoidHom
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) σ).toZModLinearMap p
      = WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) p σ := LinearMap.ext fun _ => rfl
  rw [h2, hσ, map_one] at h1
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  rw [ZMod.val_one, pow_one] at h1
  exact h1

#print axioms solution

end S_WeierstrassCurve_apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_apply_eq_self_of_galoisRep_eq_one_of_pow_eq_one (solution)
