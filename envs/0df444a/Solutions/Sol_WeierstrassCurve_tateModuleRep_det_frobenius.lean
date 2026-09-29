-- Prove2me | solution 1 for WeierstrassCurve.tateModuleRep_det_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f40e238c-8add-5e35-845e-82d55fa3ad4f

import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.LinearAlgebra.Determinant
import Theorems.Thm_WeierstrassCurve_tateModuleRep_detIsCyclotomic
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_prime_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_tateModuleRep_det_frobenius
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

private lemma padic_sep {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (h : ∀ n : ℕ, x ∈ Ideal.span {((p ^ n : ℕ) : ℤ_[p])}) : x = 0 := by
  by_contra hx
  have hv : x.valuation + 1 ≤ x.valuation := by
    refine (PadicInt.mem_span_pow_iff_le_valuation x hx _).mp ?_
    have h2 := h (x.valuation + 1)
    rwa [Nat.cast_pow] at h2
  omega

theorem solution (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    LinearMap.det ((W.tateModuleRep p hcard).ρ σ) = (ℓ : ℤ_[p]) := by
  have hmem : ∀ n : ℕ,
      LinearMap.det ((W.tateModuleRep p hcard).ρ σ) - ((ℓ : ℕ) : ℤ_[p]) ∈
        Ideal.span {((p ^ n : ℕ) : ℤ_[p])} := fun n =>
    (W.tateModuleRep_detIsCyclotomic p hΔ hcard).2 n σ ℓ fun μ hμ => ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_prime_pow_eq_one Fact.out hℓ hℓp A hA hσ n μ hμ
  exact sub_eq_zero.mp (padic_sep hmem)

end S_WeierstrassCurve_tateModuleRep_det_frobenius
end P2MW
export P2MW.S_WeierstrassCurve_tateModuleRep_det_frobenius (solution)
