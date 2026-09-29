-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/dc4a7b52-10e5-588c-a82d-b2ab9e9776a0

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isLevelPStructure_of_isLevel_of_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_isLevelPStructure
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_isSectionThrough
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_RawDrinfeldPair_IsLevel_exists_isSectionThrough_of_isUnit
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_isSectionTransport
import Theorems.Thm_ModularCurve_LevelP_BasisRing_etale
import Theorems.Thm_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : Type) [CommRing A]
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (W : WeierstrassCurve (DualNumber Ω)) (hW : IsUnit W.Δ)
    (z₀ : RawDrinfeldPair Ω)
    (hz₀ : RawDrinfeldPair.IsLevel 𝒢 q (W.map ((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A).toRingHom) z₀) :
    ∃ z : RawDrinfeldPair (DualNumber Ω),
      RawDrinfeldPair.IsLevel 𝒢 q W z ∧ 𝒯.map ((TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A) z = z₀ := by
  classical
  set fstA : DualNumber Ω →ₐ[A] Ω := (TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A with hfstA
  set W₀ : WeierstrassCurve Ω := W.map fstA.toRingHom with hW₀

  have hqO : IsUnit ((q : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hqΩ
  have hqT : IsUnit ((q : ℕ) : DualNumber Ω) := by
    have := hqO.map (algebraMap Ω (DualNumber Ω)); rwa [map_natCast] at this
  have hW₀Δ : IsUnit W₀.Δ := by rw [hW₀, WeierstrassCurve.map_Δ]; exact hW.map _
  haveI : W₀.IsElliptic := ⟨hW₀Δ⟩

  obtain ⟨⟨xP, yP, hP⟩, ⟨xQ, yQ, hQ⟩⟩ :=
    WeierstrassCurve.DrinfeldGlobal.RawDrinfeldPair.IsLevel.exists_isSectionThrough_of_isUnit q A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯
      W₀ hqO z₀ hz₀
  set D₀ : ModularCurve.LevelPData Ω := ⟨xP, yP, xQ, yQ⟩ with hD₀

  have hD₀lev : ModularCurve.IsLevelPStructure W₀ q D₀ :=
    WeierstrassCurve.DrinfeldGlobal.isLevelPStructure_of_isLevel_of_isSectionThrough A 𝒢 h𝒢 h𝒢O q hq2 𝒯 h𝒯 hqO
      W₀ z₀ hz₀ D₀ hP hQ

  have hodd : Odd q := (Fact.out : q.Prime).eq_two_or_odd'.resolve_left hq2
  have hEt : Algebra.Etale (DualNumber Ω) (ModularCurve.LevelP.BasisRing W q) :=
    ModularCurve.LevelP.BasisRing.etale W hodd (hqT.mul hW)
  haveI := hEt.formallyEtale
  obtain ⟨ψ₀, hψ₀base, hψ₀D⟩ :=
    ModularCurve.LevelP.BasisRing.exists_ringHom_basisData_map_eq W q fstA.toRingHom D₀ (by rw [← hW₀]; exact hD₀lev)
  letI instΩ : Algebra (DualNumber Ω) Ω := TrivSqZeroExt.algebraBase (R' := Ω) (M := Ω)
  have halgΩ : ∀ b : DualNumber Ω, algebraMap (DualNumber Ω) Ω b = fstA b := fun b => rfl
  let g : DualNumber Ω →ₐ[DualNumber Ω] Ω := Algebra.ofId (DualNumber Ω) Ω
  have hgsurj : Function.Surjective g := fun c => ⟨TrivSqZeroExt.inl c, rfl⟩
  have hgker : IsNilpotent (RingHom.ker (g : DualNumber Ω →+* Ω)) := by
    have hker : RingHom.ker (g : DualNumber Ω →+* Ω) = TrivSqZeroExt.kerIdeal Ω Ω := by
      ext x; rfl
    refine ⟨2, ?_⟩
    rw [hker, TrivSqZeroExt.kerIdeal_sq]
    rfl
  let f : ModularCurve.LevelP.BasisRing W q →ₐ[DualNumber Ω] Ω :=
    { toRingHom := ψ₀
      commutes' := fun b => by
        show ψ₀ (algebraMap (DualNumber Ω) (ModularCurve.LevelP.BasisRing W q) b) = fstA b
        rw [ModularCurve.LevelP.BasisRing.algebraMap_eq, ← RingHom.comp_apply, hψ₀base]
        rfl }
  let ψ : ModularCurve.LevelP.BasisRing W q →ₐ[DualNumber Ω] DualNumber Ω :=
    Algebra.FormallySmooth.liftOfSurjective f g hgsurj hgker
  have hψ : g.comp ψ = f := Algebra.FormallySmooth.comp_liftOfSurjective f g hgsurj hgker
  set D : ModularCurve.LevelPData (DualNumber Ω) := (ModularCurve.LevelP.basisData W q).map ψ.toRingHom with hD
  have hDlev : ModularCurve.IsLevelPStructure W q D := by
    have h := (ModularCurve.LevelP.isLevelPStructure_basisData W q).map ψ.toRingHom
    have hc : (ModularCurve.LevelP.basisCurve W q).map ψ.toRingHom = W := by
      rw [ModularCurve.LevelP.basisCurve, WeierstrassCurve.map_map, ← ModularCurve.LevelP.BasisRing.algebraMap_eq,
        AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, Algebra.algebraMap_self, WeierstrassCurve.map_id]
    rw [hc] at h
    exact h
  have hDfst : D.map fstA.toRingHom = D₀ := by
    rw [hD, ModularCurve.LevelPData.map_map, ← hψ₀D]
    congr 1
    have := congrArg AlgHom.toRingHom hψ
    exact this

  obtain ⟨S, hS, -⟩ := WeierstrassCurve.DrinfeldGlobal.existsUnique_isSectionThrough W D.xP D.yP hDlev.equation_P
  obtain ⟨S', hS', -⟩ := WeierstrassCurve.DrinfeldGlobal.existsUnique_isSectionThrough W D.xQ D.yQ hDlev.equation_Q

  have hDB := WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isSectionThrough_of_isLevelPStructure 𝒢 h𝒢 h𝒢O q hq2
    hqT W hW D hDlev S S' hS hS'
  let z : RawDrinfeldPair (DualNumber Ω) := ⟨W, S, S'⟩
  have hzlev : RawDrinfeldPair.IsLevel 𝒢 q W z := ⟨rfl, hW, hDB⟩
  refine ⟨z, hzlev, ?_⟩

  obtain ⟨hmP, hmQ⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_isSectionTransport A 𝒢 q 𝒯 h𝒯 fstA z
    (hCO _ _ fstA W) D hS hS'
  obtain ⟨hc, -⟩ := h𝒯.2 _ _ fstA z
  have hz₀c : z₀.curve = W₀ := hz₀.1
  have hxP : fstA D.xP = xP := congrArg ModularCurve.LevelPData.xP hDfst
  have hyP : fstA D.yP = yP := congrArg ModularCurve.LevelPData.yP hDfst
  have hxQ : fstA D.xQ = xQ := congrArg ModularCurve.LevelPData.xQ hDfst
  have hyQ : fstA D.yQ = yQ := congrArg ModularCurve.LevelPData.yQ hDfst
  rw [hxP, hyP] at hmP
  rw [hxQ, hyQ] at hmQ

  have key : ∀ (u v : RawDrinfeldPair Ω), u.curve = W₀ → v.curve = W₀ →
      IsSectionThrough u.P xP yP → IsSectionThrough v.P xP yP →
      IsSectionThrough u.Q xQ yQ → IsSectionThrough v.Q xQ yQ → u = v := by
    rintro ⟨cu, Pu, Qu⟩ ⟨cv, Pv, Qv⟩ hu hv h1 h2 h3 h4
    simp only at hu hv
    subst hu; subst hv
    obtain ⟨wP, -, huniqP⟩ := WeierstrassCurve.DrinfeldGlobal.existsUnique_isSectionThrough W₀ xP yP hD₀lev.equation_P
    obtain ⟨wQ, -, huniqQ⟩ := WeierstrassCurve.DrinfeldGlobal.existsUnique_isSectionThrough W₀ xQ yQ hD₀lev.equation_Q
    have e1 : Pu = Pv := (huniqP Pu h1).trans (huniqP Pv h2).symm
    have e2 : Qu = Qv := (huniqQ Qu h3).trans (huniqQ Qv h4).symm
    subst e1
    subst e2
    rfl
  exact key _ _ (hc.trans hW₀.symm) hz₀c hmP hP hmQ hQ

end S_WeierstrassCurve_DrinfeldGlobal_exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isLevel_and_map_fstHom_eq_dualNumber_of_isLevel (solution)
