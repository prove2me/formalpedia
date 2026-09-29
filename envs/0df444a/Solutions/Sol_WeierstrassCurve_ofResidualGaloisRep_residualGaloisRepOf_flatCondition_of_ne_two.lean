-- Prove2me | solution 1 for WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fda984b4-c197-5eca-8f8c-47163091434a

import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_baseChangeAlong
import Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_detIsCyclotomic
import Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt
import Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid HomogeneousIdealQuotientGrading.quotGradingGradedMonoid HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassProjModel.schemeHomOverComp_coe WeierstrassProjModel.RelativeGroupLaw.mk.sizeOf_spec WeierstrassProjModel.RelativeGroupLaw.nsmul_zero WeierstrassProjModel.RelativeGroupLaw.nsmul_succ WeierstrassProjModel.projModelHomogeneousIdealCR_toIdeal WeierstrassProjModel.RelativeGroupLaw.mk.injEq WeierstrassProjModel.RelativeGroupLaw.mem_torsionSubset HomogeneousIdealQuotientGrading.pieceHom_coe HomogeneousIdealQuotientGrading.quotDecompose_mk HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

theorem solution
    (𝒪 : Type) [CommRing 𝒪] {k : Type} [Field k] [Finite k] [Algebra 𝒪 k]
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ι : ZMod p →+* k)
    (hgood : W.IsGoodPrimeFor p)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    {S : Finset ℕ} (hpS : p ∈ S) (hS : ∀ q : ℕ, q.Prime → q ∉ S → W.IsGoodPrimeFor q) :
    GaloisRep.flatCondition 𝒪 p S (GaloisRepAdic.ofResidualGaloisRep
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι)) := by
  have hι : IsLocalHom ι := inferInstance
  have hΔ : (W.map (Int.castRingHom ℚ)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, eq_intCast, Int.cast_ne_zero]
    exact fun h => hgood (h ▸ dvd_zero _)
  have hflat := W.ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two p hp2 ι hgood hcard hker
  change GaloisRep.flatCondition 𝒪 p S ((GaloisRepAdic.ofResidualGaloisRep
    ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).baseChangeAlong ι hι)
  exact ⟨GaloisRepAdic.detIsCyclotomic_baseChangeAlong ι hι _
      ((W.map (Int.castRingHom ℚ)).ofResidualGaloisRep_residualGaloisRepOf_detIsCyclotomic
        p hΔ hcard hker),
    hflat,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_baseChangeAlong ι hι _
      (W.ofResidualGaloisRep_residualGaloisRepOf_isUnramifiedAt p hcard hker hq
        (fun h => hqS (h ▸ hpS)) (hS q hq hqS))⟩

end S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two
end P2MW
export P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two (solution)
