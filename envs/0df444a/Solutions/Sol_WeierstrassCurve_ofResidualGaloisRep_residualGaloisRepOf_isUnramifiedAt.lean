-- Prove2me | solution 1 for WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9c45272d-f083-50d8-be20-78a88124f2cf

import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open IsLocalRing Module Polynomial
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hgood : W.IsGoodPrimeFor q) :
    (GaloisRepAdic.ofResidualGaloisRep
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).IsUnramifiedAt q := by
  exact WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_of_isGoodPrimeFor
    (W.map (Int.castRingHom ℚ)) ⟨1, one_smul _ _⟩ p hcard hker hq hqp hgood

end S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt
end P2MW
export P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt (solution)
