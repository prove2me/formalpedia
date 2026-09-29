-- Prove2me | solution 1 for WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e756f520-2efa-5315-a727-18d3ea57c87a

import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor
import Theorems.Thm_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two
p2m_attr_erase "instance" "HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid HomogeneousIdealQuotientGrading.quotGradingGradedMonoid HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "WeierstrassProjModel.schemeHomOverComp_coe WeierstrassProjModel.RelativeGroupLaw.mk.sizeOf_spec WeierstrassProjModel.RelativeGroupLaw.nsmul_zero WeierstrassProjModel.RelativeGroupLaw.nsmul_succ WeierstrassProjModel.projModelHomogeneousIdealCR_toIdeal WeierstrassProjModel.RelativeGroupLaw.mk.injEq WeierstrassProjModel.RelativeGroupLaw.mem_torsionSubset HomogeneousIdealQuotientGrading.pieceHom_coe HomogeneousIdealQuotientGrading.quotDecompose_mk HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

namespace LCMazurOddFlat

private theorem isFlatAt_top_level {k : Type} [Field k] (ρ : GaloisRepAdic k) (p : ℕ) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (ρ.V ⧸ ((⊤ : Ideal k) • (⊤ : Submodule k ρ.V))),
        (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.levelAction ⊤ σ (e f) := by
  haveI hq : Subsingleton (ρ.V ⧸ ((⊤ : Ideal k) • (⊤ : Submodule k ρ.V))) :=
    Submodule.Quotient.subsingleton_iff.mpr (Submodule.top_smul _)
  haveI hw : Subsingleton
      (WithConv (GaloisRep.ratLocalizedAt p →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
    ⟨fun x y => WithConv.ext (Subsingleton.elim _ _)⟩
  refine ⟨GaloisRep.ratLocalizedAt p, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨fun _ => 0, fun _ => WithConv.toConv (Algebra.ofId _ _),
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _, fun _ _ _ _ => Subsingleton.elim _ _⟩

private theorem isFlatAt_ofResidualGaloisRep_residualGaloisRepOf (W : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] (hp2 : p ≠ 2) (hgood : W.IsGoodPrimeFor p)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p)) :
    (GaloisRepAdic.ofResidualGaloisRep
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).IsFlatAt p := by
  refine ⟨Finite.of_surjective _ IsLocalRing.residue_surjective, fun I _ => ?_⟩
  rcases Ideal.eq_bot_or_top I with rfl | rfl
  · have h := W.exists_finiteFlat_hopf_model_torsion_pow_of_isGoodPrimeFor p hgood hp2 1 Nat.one_pos
    rw [pow_one] at h
    obtain ⟨H, _, _, hfin, hflat, hcocomm, e₀, he_add, he_act⟩ := h
    set ρ₀ := GaloisRepAdic.ofResidualGaloisRep
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)
    let q : ρ₀.V ≃ (ρ₀.V ⧸ ((⊥ : Ideal (ZMod p)) • (⊤ : Submodule (ZMod p) ρ₀.V))) :=
      (Submodule.quotEquivOfEqBot _ (by simp)).symm.toEquiv
    refine ⟨H, ‹_›, ‹_›, hfin, hflat, hcocomm, e₀.trans q, fun f g => ?_, fun σ f g hfg => ?_⟩
    · show q (e₀ (f * g)) = q (e₀ f) + q (e₀ g)
      rw [he_add]
      rfl
    · show q (e₀ g) = ρ₀.levelAction ⊥ σ (q (e₀ f))
      rw [he_act σ f g hfg]
      rfl
  · exact isFlatAt_top_level _ p

end LCMazurOddFlat

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {k : Type} [Field k] [Finite k]
    (ι : ZMod p →+* k) (hgood : W.IsGoodPrimeFor p)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p)) :
    (GaloisRepAdic.ofResidualGaloisRep
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι)).IsFlatAt p := by
  have hι : IsLocalHom ι := inferInstance
  haveI : Finite (IsLocalRing.ResidueField k) :=
    Finite.of_surjective _ IsLocalRing.residue_surjective
  change ((GaloisRepAdic.ofResidualGaloisRep
    ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).baseChangeAlong ι hι).IsFlatAt p
  exact GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField ι hι _
    (LCMazurOddFlat.isFlatAt_ofResidualGaloisRep_residualGaloisRepOf W p hp2 hgood hcard hker)

end S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two
end P2MW
export P2MW.S_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isFlatAt_of_ne_two (solution)
