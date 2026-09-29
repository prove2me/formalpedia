-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_rat_torsionBy_withConv_equiv_algClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a3889664-da19-5385-8455-7f7ccc3af759

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two
import Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval
import Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_algClosure
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option maxHeartbeats 3200000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem solution
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra ℚ A),
      Module.Finite ℚ A ∧ Coalgebra.IsCocomm ℚ A ∧
      ∃ eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃
            Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by
  by_cases hE : E.IsElliptic
  · haveI := hE
    haveI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
    obtain ⟨hbc, G, ev, hev⟩ :=
      WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two E.toProjective
    exact WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_relativeGroupLaw_isPointsEval
      ℚ E p hbc G ev hev
  · exact WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero
      ℚ E hE p

end S_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_algClosure
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_rat_torsionBy_withConv_equiv_algClosure (solution)
