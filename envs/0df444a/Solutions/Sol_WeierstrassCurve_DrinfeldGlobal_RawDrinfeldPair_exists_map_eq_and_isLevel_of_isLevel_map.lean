-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.exists_map_eq_and_isLevel_of_isLevel_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/26f43e27-0d73-5b42-b62e-ef618c2fd7d2

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_section_comp_eq_of_isFractionRing
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_projMap_comp_projModelStrCR_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comp_projMap_eq_at_field_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_one_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_basisDivisor_comap_fst_eq_basisDivisor_comap_theta
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_eq_mk_of_comp_projMap_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_theta_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_flat_basisDivisor_subschemeIota_comp_snd
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_flat_of_comap_pullback_fst_eq
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_smoothOfRelativeDimension_one
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Theorems.Thm_WeierstrassProjModel_isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
import Theorems.Thm_AlgebraicGeometry_ext_of_isSeparated_of_dense_iUnion_range_of_comp_eq
import Theorems.Thm_WeierstrassProjModel_isProper_and_isIntegral_and_isReduced_selfPullback_pullback_snd_of_baseChangeIso
import Theorems.Thm_WeierstrassProjModel_projModel_pullback_iso_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_exists_map_eq_and_isLevel_of_isLevel_map
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec"
p2m_attr_erase "simp" "MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel NeronModelInfra

theorem solution
    (A : Type u) [CommRing A] (q : ℕ) [Fact q.Prime]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (K : Type u) [Field K] [Algebra A K]
    (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra A R₀] [Algebra R₀ K]
    [IsScalarTower A R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (hΔ₀ : IsUnit W₀.Δ)
    (z' : RawDrinfeldPair K)
    (hz' : RawDrinfeldPair.IsLevel 𝒢 q (W₀.map (IsScalarTower.toAlgHom A R₀ K).toRingHom) z') :
    ∃ z₀ : RawDrinfeldPair R₀, 𝒯.map (IsScalarTower.toAlgHom A R₀ K) z₀ = z' ∧ RawDrinfeldPair.IsLevel 𝒢 q W₀ z₀ := by
  classical

  set ι : R₀ →ₐ[A] K := IsScalarTower.toAlgHom A R₀ K with hι
  have hf : ι.toRingHom = algebraMap R₀ K := RingHom.ext fun r => IsScalarTower.toAlgHom_apply A R₀ K r
  have hSpec : Spec.map (CommRingCat.ofHom ι.toRingHom) = Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := by
    rw [hf]
  obtain ⟨φ, hφ, hφc⟩ := hCO R₀ K ι W₀
  have hsq : Proj.map φ hφ ≫ projModelStrCR W₀ =
      projModelStrCR (W₀.map ι.toRingHom) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom) :=
    WeierstrassCurve.DrinfeldGlobal.projMap_comp_projModelStrCR_of_isCoefficientHom W₀ ι.toRingHom φ hφ hφc
  obtain ⟨c, P', Q'⟩ := z'
  obtain ⟨hc, hΔ', hDB⟩ := hz'
  subst hc

  have hsP : (P'.1 ≫ Proj.map φ hφ) ≫ projModelStrCR W₀ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := by
    rw [Category.assoc, hsq, ← Category.assoc, P'.2, Category.id_comp, hf]
  have hsQ : (Q'.1 ≫ Proj.map φ hφ) ≫ projModelStrCR W₀ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := by
    rw [Category.assoc, hsq, ← Category.assoc, Q'.2, Category.id_comp, hf]
  obtain ⟨P₀, hP₀, -⟩ := WeierstrassCurve.DrinfeldGlobal.existsUnique_section_comp_eq_of_isFractionRing W₀ _ hsP
  obtain ⟨Q₀, hQ₀, -⟩ := WeierstrassCurve.DrinfeldGlobal.existsUnique_section_comp_eq_of_isFractionRing W₀ _ hsQ
  rw [← hSpec] at hP₀ hQ₀
  let z₀ : RawDrinfeldPair R₀ := ⟨W₀, P₀, Q₀⟩
  refine ⟨z₀, ?transport, rfl, hΔ₀, ?drinfeld⟩
  case transport =>

    exact WeierstrassCurve.DrinfeldGlobal.LevelTransport.map_eq_mk_of_comp_projMap_eq A 𝒢 q 𝒯 h𝒯 R₀ K ι z₀ P' Q'
      φ hφ hφc hP₀.symm hQ₀.symm
  case drinfeld =>

    show basisDivisor (𝒢 R₀ W₀ hΔ₀) q P₀ Q₀ = torsionIdeal (𝒢 R₀ W₀ hΔ₀) q
    haveI : W₀.IsElliptic := ⟨hΔ₀⟩

    have h3a : Flat ((basisDivisor (𝒢 R₀ W₀ hΔ₀) q P₀ Q₀).subschemeι ≫
        pullback.snd (projModelStrCR W₀) (𝟙 _)) :=
      WeierstrassCurve.DrinfeldGlobal.flat_basisDivisor_subschemeIota_comp_snd W₀ hΔ₀ (𝒢 R₀ W₀ hΔ₀) q P₀ Q₀

    obtain ⟨ev, hev⟩ := h𝒢 R₀ W₀ hΔ₀
    have hK3 : Flat ((𝒢 R₀ W₀ hΔ₀).schemeKerStr q) :=
      (WeierstrassProjModel.isFinite_and_flat_schemeKerStr_of_isPointsEval_of_isElliptic W₀ (𝒢 R₀ W₀ hΔ₀) ev hev
        (Fact.out : q.Prime).pos).2.1
    have h3b : Flat ((torsionIdeal (𝒢 R₀ W₀ hΔ₀) q).subschemeι ≫
        pullback.snd (projModelStrCR W₀) (𝟙 _)) :=
      WeierstrassCurve.DrinfeldGlobal.flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr W₀ (𝒢 R₀ W₀ hΔ₀) q hK3

    obtain ⟨θ, hθ₁, hθ₂⟩ :=
      WeierstrassCurve.DrinfeldGlobal.exists_theta_of_isCoefficientHom W₀ ι.toRingHom φ hφ hφc
    have h2 := WeierstrassCurve.DrinfeldGlobal.basisDivisor_comap_fst_eq_basisDivisor_comap_theta A 𝒢 h𝒢 h𝒢O R₀ K ι
      W₀ hΔ₀ hΔ' q φ hφ hφc P₀ Q₀ P' Q' hP₀.symm hQ₀.symm θ hθ₁ hθ₂
    have h3 := WeierstrassCurve.DrinfeldGlobal.torsionIdeal_comap_fst_eq_torsionIdeal_comap_theta A 𝒢 h𝒢 h𝒢O R₀ K ι
      W₀ hΔ₀ hΔ' q φ hφ hφc θ hθ₁ hθ₂
    have hDBθ : (basisDivisor (𝒢 K (W₀.map ι.toRingHom) hΔ') q P' Q').comap θ =
        (torsionIdeal (𝒢 K (W₀.map ι.toRingHom) hΔ') q).comap θ := congrArg (fun J => J.comap θ) hDB
    have h3c :
        (basisDivisor (𝒢 R₀ W₀ hΔ₀) q P₀ Q₀).comap
            (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom (algebraMap R₀ K)))) =
          (torsionIdeal (𝒢 R₀ W₀ hΔ₀) q).comap
            (pullback.fst (pullback.snd (projModelStrCR W₀) (𝟙 _)) (Spec.map (CommRingCat.ofHom (algebraMap R₀ K)))) := by
      rw [← hSpec]
      exact h2.trans (hDBθ.trans h3.symm)
    haveI := h3a; haveI := h3b
    exact AlgebraicGeometry.Scheme.IdealSheafData.eq_of_flat_of_comap_pullback_fst_eq K
      (pullback.snd (projModelStrCR W₀) (𝟙 _)) _ _ h3c

end S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_exists_map_eq_and_isLevel_of_isLevel_map
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_exists_map_eq_and_isLevel_of_isLevel_map (solution)
