-- Prove2me | solution 1 for WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/12ffb73e-589a-51d5-be74-b7401397f17d

import Theorems.Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_goodReduction
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff
import Theorems.Thm_WeierstrassCurve_IsIntegralModelOf_exists_linearEquiv_torsionBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel (galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hgood : W.IsGoodPrimeFor q) :
    (E.residualGaloisRepOf p hcard hker).IsUnramifiedAt q := by
  rw [WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_iff]

  have hW' : GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p q :=
    WeierstrassCurve.galoisRepUnramifiedAt_of_goodReduction W hq (Fact.out) (Ne.symm hqp) hgood

  obtain ⟨φ, hφ⟩ := hW.exists_linearEquiv_torsionBy p
  intro A hA σ hσ x
  apply φ.injective
  rw [hφ σ x]
  exact hW' A hA σ hσ (φ x)

end S_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor
end P2MW
export P2MW.S_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor (solution)
