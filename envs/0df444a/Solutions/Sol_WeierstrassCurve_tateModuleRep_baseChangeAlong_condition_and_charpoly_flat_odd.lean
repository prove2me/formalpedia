-- Prove2me | solution 1 for WeierstrassCurve.tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e7c642be-53f3-5943-873f-a2c2094c8322

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_Algebra_PatchingDatum
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_charpoly_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isUnramifiedAt_baseChangeAlong
import Theorems.Thm_WeierstrassCurve_tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor
import Theorems.Thm_WeierstrassCurve_tateModuleRep_detIsCyclotomic
import Theorems.Thm_WeierstrassCurve_tateModuleRep_isOrdinaryAt
import Theorems.Thm_WeierstrassCurve_tateModuleRep_charpoly_frobenius
import Theorems.Thm_WeierstrassCurve_tateModuleRep_isFlatAt
import Theorems.Thm_WeierstrassCurve_exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor
import Theorems.Thm_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid HomogeneousIdealQuotientGrading.quotGradingGradedMonoid HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassProjModel.schemeHomOverComp_coe WeierstrassProjModel.RelativeGroupLaw.mk.sizeOf_spec WeierstrassProjModel.RelativeGroupLaw.nsmul_zero WeierstrassProjModel.RelativeGroupLaw.nsmul_succ WeierstrassProjModel.projModelHomogeneousIdealCR_toIdeal WeierstrassProjModel.RelativeGroupLaw.mk.injEq WeierstrassProjModel.RelativeGroupLaw.mem_torsionSubset HomogeneousIdealQuotientGrading.pieceHom_coe HomogeneousIdealQuotientGrading.quotDecompose_mk HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) →
      GaloisRep.ordinaryCondition 𝒪 p S
        (((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).baseChangeAlong
          (GaloisRep.padicIntToRing 𝒪 p hp𝒪) (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp𝒪))) ∧
    (p ≠ 2 → W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p →
      GaloisRep.flatCondition 𝒪 p S
        (((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).baseChangeAlong
          (GaloisRep.padicIntToRing 𝒪 p hp𝒪) (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp𝒪))) ∧
    (∀ (ℓ : ℕ), ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly ((((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).baseChangeAlong
            (GaloisRep.padicIntToRing 𝒪 p hp𝒪) (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp𝒪)).ρ σ) =
            X ^ 2 - C ((W.apOfModel ℓ : ℤ) : 𝒪) * X + C ((ℓ : 𝒪))) := by
  have _ := hS

  have hΔℚ : (W.map (Int.castRingHom ℚ)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    exact fun h => hΔ (Int.cast_injective (h.trans (Int.cast_zero).symm))

  have hdet : ((((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).baseChangeAlong
      (GaloisRep.padicIntToRing 𝒪 p hp𝒪) (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp𝒪))).DetIsCyclotomic p :=
    GaloisRepAdic.detIsCyclotomic_baseChangeAlong _ _ _ (WeierstrassCurve.tateModuleRep_detIsCyclotomic (W.map (Int.castRingHom ℚ)) p hΔℚ hcard)

  have hunr : ∀ q : ℕ, q.Prime → q ∉ S →
      ((((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).baseChangeAlong
        (GaloisRep.padicIntToRing 𝒪 p hp𝒪) (GaloisRep.isLocalHom_padicIntToRing 𝒪 p hp𝒪))).IsUnramifiedAt q := by
    intro q hq hqS
    have hqp : q ≠ p := fun h => hqS (h ▸ hpS)
    have hgoodq : W.IsGoodPrimeFor q := fun hdvd => hqS (hbadS q hq hdvd)
    exact GaloisRepAdic.isUnramifiedAt_baseChangeAlong _ _ _
      (W.tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor p hcard hq hqp hgoodq)
  refine ⟨fun hord => ⟨hdet, ?_, hunr⟩, fun hp2 hgood _ => ⟨hdet, ?_, hunr⟩, ?_⟩
  · exact GaloisRepAdic.isOrdinaryAt_baseChangeAlong _ _ _ (WeierstrassCurve.tateModuleRep_isOrdinaryAt W p hΔ hW hcard hord)
  · have hflat0 : ((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).IsFlatAt p :=
      WeierstrassCurve.tateModuleRep_isFlatAt (W.map (Int.castRingHom ℚ)) p hcard
        (W.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor p hgood hp2)
    exact GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField _ _ _ hflat0
  · intro ℓ hℓ hgood hℓS A hA σ hσ
    have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hpS)
    rw [GaloisRepAdic.charpoly_baseChangeAlong, WeierstrassCurve.tateModuleRep_charpoly_frobenius W p hcard ℓ hℓ hgood hℓp A hA σ hσ]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, map_intCast, map_natCast, Polynomial.map_intCast, Polynomial.map_natCast]

end S_WeierstrassCurve_tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd
end P2MW
export P2MW.S_WeierstrassCurve_tateModuleRep_baseChangeAlong_condition_and_charpoly_flat_odd (solution)
