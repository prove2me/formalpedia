-- Prove2me | solution 1 for V3Asm.edgePt_transversal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3412d210-19bb-57b9-8d15-6cab79e82fb3

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSite
import Theorems.Thm_ModularCurve_DRModelPackage_exists_eq_baseChangeMap_crossing_of_mem_closure_of_mem_closure
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing
import Theorems.Thm_ModularCurve_DRModelPackage_eq_baseChangeMap_genericPoint_of_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Asm_edgePt_transversal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_edgePt_transversal.AlgebraicGeometry"

section E80Ws24

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_edgePt_transversal.AlgebraicGeometry ModularCurve Topology"

namespace V3Asm
p2m_export "V3Asm" "πX bc SiteHyps R C D Y toBase hq mem_X0_iff width hRF p_mem_maximalIdeal ξ ξ_zero ξ_one vertex_eq oRes hoRes gRes hgRes comp η edgePt chainPos'_eq"
p2m_open "V3Asm"

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) (H : V3Asm.SiteHyps p 𝔛 O κ toκ)

theorem C_x (n : V3Glue.Site.Node p 𝔛 κ) :
    (V3Asm.C p 𝔛 O κ toκ hϖ H).x n = V3Glue.Site.xpt 𝔛 (V3Asm.bc p O κ toκ) n := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem ξ_specializes_xpt (n : V3Glue.Site.Node p 𝔛 κ) (j : Fin 2) :
    V3Asm.ξ p 𝔛 O κ toκ j ⤳ V3Glue.Site.xpt 𝔛 (V3Asm.bc p O κ toκ) n := by
  have h := ModularCurve.DRModelPackage.baseChangeMap_genericPoint_specializes_crossing p 𝔛 O κ toκ n
  revert j
  refine Fin.cases ?_ (fun i => ?_)
  · exact h.1
  · have : i = 0 := Subsingleton.elim _ _
    subst this
    exact h.2

theorem ξ_specializes_x (n : V3Glue.Site.Node p 𝔛 κ) (j : Fin 2) :
    V3Asm.ξ p 𝔛 O κ toκ j ⤳ (V3Asm.C p 𝔛 O κ toκ hϖ H).x n :=
  ξ_specializes_xpt p 𝔛 O κ toκ n j

theorem ξ_mem_U (n : V3Glue.Site.Node p 𝔛 κ) (j : Fin 2) :
    V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).U n :=
  (ξ_specializes_x p 𝔛 O hϖ κ toκ H n j).mem_open ((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).isOpen
    ((V3Asm.C p 𝔛 O κ toκ hϖ H).x_mem_U n)

theorem xU_mem_closure_ξ (n : V3Glue.Site.Node p 𝔛 κ) (j : Fin 2) :
    (V3Asm.C p 𝔛 O κ toκ hϖ H).xU n ∈
      closure ({⟨V3Asm.ξ p 𝔛 O κ toκ j, ξ_mem_U p 𝔛 O hϖ κ toκ H n j⟩} : Set ↥((V3Asm.C p 𝔛 O κ toκ hϖ H).U n)) := by
  rw [← specializes_iff_mem_closure]
  exact Topology.IsInducing.subtypeVal.specializes_iff.mp (ξ_specializes_x p 𝔛 O hϖ κ toκ H n j)

theorem hW0 : ∀ x : V3Glue.Site.XO p O,
    x ∈ closure ({V3Asm.ξ p 𝔛 O κ toκ 0} : Set (V3Glue.Site.XO p O)) →
    x ∈ closure ({V3Asm.ξ p 𝔛 O κ toκ 1} : Set (V3Glue.Site.XO p O)) →
    x ∉ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0 := by
  intro x h0 h1 hx
  rw [V3Asm.ξ_zero] at h0
  rw [V3Asm.ξ_one] at h1
  have h0' : x ∈ closure (Set.range ⇑(𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base) :=
    closure_mono (Set.singleton_subset_iff.mpr
      (Set.mem_range_self (f := ⇑(𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base) (genericPoint ↥(𝔛.ratModel κ).C))) h0
  have h1' : x ∈ closure (Set.range ⇑(𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base) :=
    closure_mono (Set.singleton_subset_iff.mpr
      (Set.mem_range_self (f := ⇑(𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base) (genericPoint ↥(𝔛.ratModel κ).C))) h1
  obtain ⟨n, rfl⟩ := ModularCurve.DRModelPackage.exists_eq_baseChangeMap_crossing_of_mem_closure_of_mem_closure
    p 𝔛 O hϖ κ toκ x h0' h1'
  exact ((V3Asm.mem_X0_iff p 𝔛 O κ toκ hϖ H _).mp hx) n rfl

theorem hM_ξ (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) (j : Fin 2) :
    ∀ x' : ↥(V3Asm.C p 𝔛 O κ toκ hϖ H).X0, x' ⤳ ⟨V3Asm.ξ p 𝔛 O κ toκ j, hξ j⟩ →
      (x' : V3Glue.Site.XO p O) ∉ (V3Asm.πX p O) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
      x' = ⟨V3Asm.ξ p 𝔛 O κ toκ j, hξ j⟩ := by
  have hmax := ModularCurve.DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes p 𝔛 O hϖ κ toκ
  intro x' hsp hV
  apply Subtype.ext
  have hsp' : (x' : V3Glue.Site.XO p O) ⤳ V3Asm.ξ p 𝔛 O κ toκ j := hsp.map continuous_subtype_val
  clear hsp
  revert hsp'
  revert j
  refine Fin.cases ?_ (fun i => ?_)
  · intro hsp'
    exact hmax.1 _ hV hsp'
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    intro hsp'
    exact hmax.2 _ hV hsp'

end V3Asm

end E80Ws24

section E80Ws4BL

p2m_open "AlgebraicGeometry P2MW.S_V3Asm_edgePt_transversal.AlgebraicGeometry CategoryTheory Polynomial AlgebraicGeometry.Polynomial"

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R ext induction_on' algebraMap_apply comap algebraMap_eq C monomial C_mul_X_pow_eq_monomial ringHom_ext' CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient.U_mul_V CrossingQuotient"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.toCrossing U V U_mul_V lift resolutionChart resolutionChart_U resolutionChart_V mk_surjective monomial ringHom_ext' lineVHom lineUHom lineVHom_U lineVHom_V lineUHom_U lineUHom_V originIdeal lineVIdeal lineUIdeal mem_lineVIdeal_iff mem_lineUIdeal_iff U_notMem_lineVIdeal V_notMem_lineUIdeal algebraMap_mem_lineVIdeal algebraMap_mem_lineUIdeal lineVIdeal_le_originIdeal lineUIdeal_le_originIdeal t_pow_mem branchVPrime branchUPrime one_le originIdeal_eq_span_sup_map lineUIdeal_eq_span_sup_map lineUIdeal_le_iff lineVIdeal_eq_span_sup_map lineVIdeal_le_iff Resolution.origin Resolution.lineGen Resolution.lineUGen Resolution.lineUGen_eq_lineGen Resolution.lineGen_specializes_origin Resolution.lineUGen_specializes_origin Resolution.origin_mem_closure_lineGen Resolution.origin_mem_closure_lineUGen Resolution.vertexPt Resolution.branchVPt Resolution.branchUPt"
p2m_open "MvPolynomial.CrossingQuotient MvPolynomial"

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) (ht : t ∈ 𝔭)

theorem lineVHom_surjective_of_mem : Function.Surjective (lineVHom t 𝔭 ht) := by
  intro q
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a =>
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨algebraMap W _ w * U t ^ n, ?_⟩
    rw [map_mul, map_pow, lineVHom_U, AlgHom.commutes, ← Polynomial.C_mul_X_pow_eq_monomial,
      IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X], Polynomial.algebraMap_eq,
      Ideal.Quotient.algebraMap_eq]

theorem lineUHom_surjective_of_mem : Function.Surjective (lineUHom t 𝔭 ht) := by
  intro q
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a =>
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨algebraMap W _ w * V t ^ n, ?_⟩
    rw [map_mul, map_pow, lineUHom_V, AlgHom.commutes, ← Polynomial.C_mul_X_pow_eq_monomial,
      IsScalarTower.algebraMap_apply W (W ⧸ 𝔭) (W ⧸ 𝔭)[X], Polynomial.algebraMap_eq,
      Ideal.Quotient.algebraMap_eq]

variable (e : ℕ)

theorem lineVHom_comp_resolutionChart_zero (i : Fin e) (hi : (i : ℕ) = 0) :
    (lineVHom t 𝔭 ht).toRingHom.comp (resolutionChart t e i).toRingHom =
      (lineVHom (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e (one_le e i))).toRingHom := by
  refine ringHom_ext' (t ^ e) (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U,
      lineVHom_U, hi, pow_zero, map_one, one_mul]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V, map_mul,
      lineVHom_V, mul_zero]

theorem lineUHom_comp_resolutionChart_last (i : Fin e) (hi : (i : ℕ) + 1 = e) :
    (lineUHom t 𝔭 ht).toRingHom.comp (resolutionChart t e i).toRingHom =
      (lineUHom (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e (one_le e i))).toRingHom := by
  refine ringHom_ext' (t ^ e) (fun w => ?_) ?_ ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U, map_mul,
      lineUHom_U, mul_zero]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V,
      lineUHom_V, show e - 1 - (i : ℕ) = 0 by omega, pow_zero, map_one, one_mul]

namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq toCrossing origin lineGen lineUGen lineGen_def lineUGen_def lineUGen_eq_lineGen_succ lineUGen_eq_lineGen lineGen_specializes_origin lineUGen_specializes_origin origin_mem_closure_lineGen origin_mem_closure_lineUGen vertexPt branchVPt branchUPt toCrossing_ι_apply eq_origin_of_mem_closure_lineGen_zero eq_origin_of_mem_closure_lineUGen_last"
p2m_open "MvPolynomial.CrossingQuotient.Resolution"

variable [𝔭.IsPrime]

theorem eq_lineGen_zero_of_toCrossing_eq_branchVPt (he : 1 ≤ e) (z : Resolution t e)
    (hz : toCrossing t e z = branchVPt t e 𝔭 ht he) : z = lineGen t e 𝔭 ht ⟨0, he⟩ := by
  obtain ⟨i, P, rfl⟩ := exists_ι_apply_eq t e z
  rw [toCrossing_ι_apply] at hz
  have hcomap : P.asIdeal.comap (resolutionChart t e i).toRingHom = branchVPrime t 𝔭 ht e he :=
    congrArg PrimeSpectrum.asIdeal hz

  have h𝔭 : ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P.asIdeal := by
    intro w hw
    have : algebraMap W (CrossingQuotient W (t ^ e)) w ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [hcomap]; exact algebraMap_mem_lineVIdeal _ _ _ hw
    rw [Ideal.mem_comap] at this
    simpa [AlgHom.commutes] using this

  have hUi : algebraMap W _ (t ^ (i : ℕ)) * U t ∉ P.asIdeal := by
    intro h
    have : U (t ^ e) ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [Ideal.mem_comap]; simpa [resolutionChart_U] using h
    rw [hcomap] at this
    exact U_notMem_lineVIdeal _ _ _ this
  have hi0 : (i : ℕ) = 0 := by
    by_contra hne
    apply hUi
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hk, pow_succ, map_mul, mul_assoc]
    exact P.asIdeal.mul_mem_left _ (P.asIdeal.mul_mem_right _ (h𝔭 t ht))
  have hU : U t ∉ P.asIdeal := by rw [hi0, pow_zero, map_one, one_mul] at hUi; exact hUi
  have hV : V t ∈ P.asIdeal :=
    (P.isPrime.mem_or_mem (by rw [U_mul_V]; exact h𝔭 t ht)).resolve_left hU
  have hle : lineVIdeal t 𝔭 ht ≤ P.asIdeal := (lineVIdeal_le_iff t 𝔭 ht).mpr ⟨hV, h𝔭⟩
  have key := lineVHom_comp_resolutionChart_zero t 𝔭 ht e i hi0
  have hPeq : P.asIdeal = lineVIdeal t 𝔭 ht := by
    refine le_antisymm (fun c hc => ?_) hle
    obtain ⟨d, hd⟩ := lineVHom_surjective_of_mem (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e (one_le e i)) (lineVHom t 𝔭 ht c)
    have hd' : lineVHom t 𝔭 ht (resolutionChart t e i d) = lineVHom t 𝔭 ht c := by
      rw [← hd]; exact RingHom.congr_fun key d
    have hker : c - resolutionChart t e i d ∈ lineVIdeal t 𝔭 ht := by
      rw [mem_lineVIdeal_iff, map_sub, hd', sub_self]
    have hdP : resolutionChart t e i d ∈ P.asIdeal := by
      have := P.asIdeal.sub_mem hc (hle hker)
      rwa [sub_sub_cancel] at this
    have hdB : d ∈ branchVPrime t 𝔭 ht e he := by
      rw [← hcomap, Ideal.mem_comap]; exact hdP
    rw [mem_lineVIdeal_iff, ← hd]
    exact (mem_lineVIdeal_iff (t ^ e) 𝔭 _ d).mp hdB
  have hi : i = ⟨0, he⟩ := Fin.ext hi0
  subst hi
  rw [lineGen_def]
  congr 1
  exact PrimeSpectrum.ext hPeq

theorem eq_lineUGen_last_of_toCrossing_eq_branchUPt (he : 1 ≤ e) (z : Resolution t e)
    (hz : toCrossing t e z = branchUPt t e 𝔭 ht he) : z = lineUGen t e 𝔭 ht ⟨e - 1, by omega⟩ := by
  obtain ⟨i, P, rfl⟩ := exists_ι_apply_eq t e z
  rw [toCrossing_ι_apply] at hz
  have hcomap : P.asIdeal.comap (resolutionChart t e i).toRingHom = branchUPrime t 𝔭 ht e he :=
    congrArg PrimeSpectrum.asIdeal hz
  have h𝔭 : ∀ w ∈ 𝔭, algebraMap W (CrossingQuotient W t) w ∈ P.asIdeal := by
    intro w hw
    have : algebraMap W (CrossingQuotient W (t ^ e)) w ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [hcomap]; exact algebraMap_mem_lineUIdeal _ _ _ hw
    rw [Ideal.mem_comap] at this
    simpa [AlgHom.commutes] using this
  have hVi : algebraMap W _ (t ^ (e - 1 - (i : ℕ))) * V t ∉ P.asIdeal := by
    intro h
    have : V (t ^ e) ∈ P.asIdeal.comap (resolutionChart t e i).toRingHom := by
      rw [Ideal.mem_comap]; simpa [resolutionChart_V] using h
    rw [hcomap] at this
    exact V_notMem_lineUIdeal _ _ _ this
  have hi0 : e - 1 - (i : ℕ) = 0 := by
    by_contra hne
    apply hVi
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hk, pow_succ, map_mul, mul_assoc]
    exact P.asIdeal.mul_mem_left _ (P.asIdeal.mul_mem_right _ (h𝔭 t ht))
  have hV : V t ∉ P.asIdeal := by rw [hi0, pow_zero, map_one, one_mul] at hVi; exact hVi
  have hU : U t ∈ P.asIdeal :=
    (P.isPrime.mem_or_mem (by rw [U_mul_V]; exact h𝔭 t ht)).resolve_right hV
  have hle : lineUIdeal t 𝔭 ht ≤ P.asIdeal := (lineUIdeal_le_iff t 𝔭 ht).mpr ⟨hU, h𝔭⟩
  have hilast : (i : ℕ) + 1 = e := by have := i.2; omega
  have key := lineUHom_comp_resolutionChart_last t 𝔭 ht e i hilast
  have hPeq : P.asIdeal = lineUIdeal t 𝔭 ht := by
    refine le_antisymm (fun c hc => ?_) hle
    obtain ⟨d, hd⟩ := lineUHom_surjective_of_mem (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e (one_le e i)) (lineUHom t 𝔭 ht c)
    have hd' : lineUHom t 𝔭 ht (resolutionChart t e i d) = lineUHom t 𝔭 ht c := by
      rw [← hd]; exact RingHom.congr_fun key d
    have hker : c - resolutionChart t e i d ∈ lineUIdeal t 𝔭 ht := by
      rw [mem_lineUIdeal_iff, map_sub, hd', sub_self]
    have hdP : resolutionChart t e i d ∈ P.asIdeal := by
      have := P.asIdeal.sub_mem hc (hle hker)
      rwa [sub_sub_cancel] at this
    have hdB : d ∈ branchUPrime t 𝔭 ht e he := by
      rw [← hcomap, Ideal.mem_comap]; exact hdP
    rw [mem_lineUIdeal_iff, ← hd]
    exact (mem_lineUIdeal_iff (t ^ e) 𝔭 _ d).mp hdB
  have hi : (⟨e - 1, by omega⟩ : Fin e) = i := Fin.ext (by simp; omega)
  rw [lineUGen_def, hi]
  congr 1
  exact PrimeSpectrum.ext hPeq

variable [𝔭.IsMaximal]

theorem eq_origin_zero_of_mem_closure_of_toCrossing_eq_branchVPt (he : 1 ≤ e) (o o' : Resolution t e)
    (ho : toCrossing t e o = branchVPt t e 𝔭 ht he) (ho' : o' ∈ closure ({o} : Set (Resolution t e)))
    (hv : toCrossing t e o' = vertexPt t e 𝔭 ht he) : o' = origin t e 𝔭 ht ⟨0, he⟩ := by
  have h := eq_lineGen_zero_of_toCrossing_eq_branchVPt t 𝔭 ht e he o ho
  subst h
  exact eq_origin_of_mem_closure_lineGen_zero t e 𝔭 ht he ⟨0, he⟩ rfl o' ho' hv

theorem eq_origin_last_of_mem_closure_of_toCrossing_eq_branchUPt (he : 1 ≤ e) (o o' : Resolution t e)
    (ho : toCrossing t e o = branchUPt t e 𝔭 ht he) (ho' : o' ∈ closure ({o} : Set (Resolution t e)))
    (hv : toCrossing t e o' = vertexPt t e 𝔭 ht he) : o' = origin t e 𝔭 ht ⟨e - 1, by omega⟩ := by
  have h := eq_lineUGen_last_of_toCrossing_eq_branchUPt t 𝔭 ht e he o ho
  subst h
  exact eq_origin_of_mem_closure_lineUGen_last t e 𝔭 ht he ⟨e - 1, by omega⟩ (by simp; omega) o' ho' hv

end Resolution

end MvPolynomial.CrossingQuotient

end E80Ws4BL

section E80Orient12

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_edgePt_transversal.AlgebraicGeometry MvPolynomial P2MW.S_V3Asm_edgePt_transversal.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_V3Asm_edgePt_transversal.MvPolynomial.CrossingQuotient ModularCurve Topology"

namespace V3Asm
p2m_export "V3Asm" "πX bc SiteHyps R C D Y toBase hq mem_X0_iff width hRF p_mem_maximalIdeal ξ ξ_zero ξ_one vertex_eq oRes hoRes gRes hgRes comp η edgePt chainPos'_eq"
p2m_open "V3Asm"

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) (H : V3Asm.SiteHyps p 𝔛 O κ toκ)

theorem f_ξ_zero_eq_branchVPt (n : V3Glue.Site.Node p 𝔛 κ) (hU : V3Asm.ξ p 𝔛 O κ toκ 0 ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).U n) :
    (V3Asm.C p 𝔛 O κ toκ hϖ H).f n ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩ =
      Resolution.branchVPt ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O)
        (V3Asm.p_mem_maximalIdeal p O hϖ) ((V3Asm.C p 𝔛 O κ toκ hϖ H).one_le_thick n) := by
  haveI := H.nodeFinite
  have he : 1 ≤ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n := (V3Asm.C p 𝔛 O κ toκ hϖ H).one_le_thick n
  have hpm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := V3Asm.p_mem_maximalIdeal p O hϖ

  have hle : (V3Asm.C p 𝔛 O κ toκ hϖ H).U n ≤ (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).U := (V3Asm.R p 𝔛 O κ toκ hϖ H).U_le ((V3Asm.R p 𝔛 O κ toκ hϖ H).hnbhd_of H.ET) n
  have hξ0 : (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).U.ι.base (((V3Glue.Site.XO p O).homOfLE hle).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩) = V3Asm.ξ p 𝔛 O κ toκ 0 := by
    change ((((V3Glue.Site.XO p O).homOfLE hle ≫ (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).U.ι).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩) : (V3Glue.Site.XO p O)) = _
    rw [Scheme.homOfLE_ι]
    rfl
  have hfeq : ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩ =
      (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).f.base (((V3Glue.Site.XO p O).homOfLE hle).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩) := rfl

  have hGen : CrossingQuotient.V (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∈ (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩).asIdeal := by
    rw [hfeq]
    apply (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).orient_inf_conv
    rw [hξ0, V3Asm.ξ_zero]
    exact ⟨_, rfl⟩

  have h𝔪P : ∀ w ∈ IsLocalRing.maximalIdeal O,
      algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)) w ∈ (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩).asIdeal := by
    intro w hw
    rw [hϖ, Ideal.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [map_mul]
    refine Ideal.mul_mem_right _ _ (Ideal.IsPrime.mem_of_pow_mem inferInstance ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ?_)
    first | rw [← map_pow, ← CrossingQuotient.U_mul_V] | erw [← map_pow, ← CrossingQuotient.U_mul_V] | (erw [← map_pow]; erw [← CrossingQuotient.U_mul_V])
    exact Ideal.mul_mem_left _ _ hGen

  have hspec : Resolution.branchVPt ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm he ⤳
      ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mp ((lineVIdeal_le_iff (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) _).mpr ⟨hGen, h𝔪P⟩)

  have hgen : GeneralizingMap ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base := Flat.generalizingMap ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)
  obtain ⟨y, hysp, hfy⟩ := hgen hspec

  have hover : ((V3Asm.C p 𝔛 O κ toκ hϖ H).σ n).base (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base y) = (V3Asm.πX p O).base (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) := by
    have h := congr($((V3Asm.C p 𝔛 O κ toκ hϖ H).f_over n).base y)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h
  have hσ : PrimeSpectrum.comap (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n))) (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base y) = ((V3Asm.C p 𝔛 O κ toκ hϖ H).σ n).base (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base y) := rfl
  have hnotin : (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    intro hmem
    have hmem' : (V3Asm.πX p O).base (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O) := hmem
    rw [← hover, ← hσ] at hmem'
    refine (PrimeSpectrum.mem_basicOpen _ _).mp hmem' ?_
    change algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)) ((p : ℕ) : O) ∈ (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base y).asIdeal
    rw [hfy]
    exact algebraMap_mem_lineVIdeal (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) _ hpm
  have hysp' : (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) ⤳ V3Asm.ξ p 𝔛 O κ toκ 0 := by
    have := hysp.map ((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base.hom.continuous
    exact this
  have hmax := (ModularCurve.DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes p 𝔛 O hϖ κ toκ).1
    (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) hnotin (by rw [← V3Asm.ξ_zero]; exact hysp')
  have hy : y = ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩ := by
    apply Subtype.ext
    change (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) = V3Asm.ξ p 𝔛 O κ toκ 0
    rw [hmax, V3Asm.ξ_zero]
  rw [← hy, hfy]

theorem f_ξ_one_eq_branchUPt (n : V3Glue.Site.Node p 𝔛 κ) (hU : V3Asm.ξ p 𝔛 O κ toκ 1 ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).U n) :
    (V3Asm.C p 𝔛 O κ toκ hϖ H).f n ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩ =
      Resolution.branchUPt ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O)
        (V3Asm.p_mem_maximalIdeal p O hϖ) ((V3Asm.C p 𝔛 O κ toκ hϖ H).one_le_thick n) := by
  haveI := H.nodeFinite
  have he : 1 ≤ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n := (V3Asm.C p 𝔛 O κ toκ hϖ H).one_le_thick n
  have hpm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := V3Asm.p_mem_maximalIdeal p O hϖ

  have hle : (V3Asm.C p 𝔛 O κ toκ hϖ H).U n ≤ (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).U := (V3Asm.R p 𝔛 O κ toκ hϖ H).U_le ((V3Asm.R p 𝔛 O κ toκ hϖ H).hnbhd_of H.ET) n
  have hξ0 : (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).U.ι.base (((V3Glue.Site.XO p O).homOfLE hle).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩) = V3Asm.ξ p 𝔛 O κ toκ 1 := by
    change ((((V3Glue.Site.XO p O).homOfLE hle ≫ (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).U.ι).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩) : (V3Glue.Site.XO p O)) = _
    rw [Scheme.homOfLE_ι]
    rfl
  have hfeq : ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩ =
      (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).f.base (((V3Glue.Site.XO p O).homOfLE hle).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩) := rfl

  have hGen : CrossingQuotient.U (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∈ (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩).asIdeal := by
    rw [hfeq]
    apply (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).orient_zero_conv
    rw [hξ0, V3Asm.ξ_one]
    exact ⟨_, rfl⟩

  have h𝔪P : ∀ w ∈ IsLocalRing.maximalIdeal O,
      algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)) w ∈ (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩).asIdeal := by
    intro w hw
    rw [hϖ, Ideal.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [map_mul]
    refine Ideal.mul_mem_right _ _ (Ideal.IsPrime.mem_of_pow_mem inferInstance ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ?_)
    first | rw [← map_pow, ← CrossingQuotient.U_mul_V] | erw [← map_pow, ← CrossingQuotient.U_mul_V] | (erw [← map_pow]; erw [← CrossingQuotient.U_mul_V])
    exact Ideal.mul_mem_right _ _ hGen

  have hspec : Resolution.branchUPt ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) hpm he ⤳
      ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mp ((lineUIdeal_le_iff (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) _).mpr ⟨hGen, h𝔪P⟩)

  have hgen : GeneralizingMap ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base := Flat.generalizingMap ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)
  obtain ⟨y, hysp, hfy⟩ := hgen hspec

  have hover : ((V3Asm.C p 𝔛 O κ toκ hϖ H).σ n).base (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base y) = (V3Asm.πX p O).base (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) := by
    have h := congr($((V3Asm.C p 𝔛 O κ toκ hϖ H).f_over n).base y)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h
  have hσ : PrimeSpectrum.comap (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n))) (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base y) = ((V3Asm.C p 𝔛 O κ toκ hϖ H).σ n).base (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base y) := rfl
  have hnotin : (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    intro hmem
    have hmem' : (V3Asm.πX p O).base (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O) := hmem
    rw [← hover, ← hσ] at hmem'
    refine (PrimeSpectrum.mem_basicOpen _ _).mp hmem' ?_
    change algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)) ((p : ℕ) : O) ∈ (((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base y).asIdeal
    rw [hfy]
    exact algebraMap_mem_lineUIdeal (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) _ hpm
  have hysp' : (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) ⤳ V3Asm.ξ p 𝔛 O κ toκ 1 := by
    have := hysp.map ((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base.hom.continuous
    exact this
  have hmax := (ModularCurve.DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes p 𝔛 O hϖ κ toκ).2
    (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) hnotin (by rw [← V3Asm.ξ_one]; exact hysp')
  have hy : y = ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩ := by
    apply Subtype.ext
    change (((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).ι.base y) = V3Asm.ξ p 𝔛 O κ toκ 1
    rw [hmax, V3Asm.ξ_one]
  rw [← hy, hfy]

end V3Asm

end E80Orient12

section E80ModelTransv

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R ext induction_on' algebraMap_apply comap algebraMap_eq C monomial C_mul_X_pow_eq_monomial ringHom_ext' CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient.U_mul_V CrossingQuotient"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.toCrossing U V U_mul_V lift resolutionChart resolutionChart_U resolutionChart_V mk_surjective monomial ringHom_ext' lineVHom lineUHom lineVHom_U lineVHom_V lineUHom_U lineUHom_V originIdeal lineVIdeal lineUIdeal mem_lineVIdeal_iff mem_lineUIdeal_iff U_notMem_lineVIdeal V_notMem_lineUIdeal algebraMap_mem_lineVIdeal algebraMap_mem_lineUIdeal lineVIdeal_le_originIdeal lineUIdeal_le_originIdeal t_pow_mem branchVPrime branchUPrime one_le originIdeal_eq_span_sup_map lineUIdeal_eq_span_sup_map lineUIdeal_le_iff lineVIdeal_eq_span_sup_map lineVIdeal_le_iff Resolution.origin Resolution.lineGen Resolution.lineUGen Resolution.lineUGen_eq_lineGen Resolution.lineGen_specializes_origin Resolution.lineUGen_specializes_origin Resolution.origin_mem_closure_lineGen Resolution.origin_mem_closure_lineUGen Resolution.vertexPt Resolution.branchVPt Resolution.branchUPt"
p2m_open "MvPolynomial.CrossingQuotient MvPolynomial"

p2m_open "AlgebraicGeometry P2MW.S_V3Asm_edgePt_transversal.AlgebraicGeometry IsLocalRing"

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) [𝔭.IsPrime] (ht : t ∈ 𝔭)

theorem originIdeal_eq_lineVIdeal_sup_lineUIdeal :
    originIdeal t 𝔭 ht = lineVIdeal t 𝔭 ht ⊔ lineUIdeal t 𝔭 ht := by
  rw [originIdeal_eq_span_sup_map, lineVIdeal_eq_span_sup_map, lineUIdeal_eq_span_sup_map, Ideal.span_insert]
  ac_rfl

end MvPolynomial.CrossingQuotient

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective StructureSheaf.toStalk_stalkSpecializes Scheme.Hom StructureSheaf.stalkAlgebra Spec StructureSheaf.toStalk Spec.map Scheme IsOpenImmersion Scheme.Hom.comp_base Flat Etale StructureSheaf.IsLocalization.to_stalk Scheme.homOfLE_ι Flat.generalizingMap Scheme.Hom.comp_apply v3genPrime_sup_genPrime_eq_maximalIdeal_of_stalkMap_bijective IsOpenImmersion.v3_stalkMap_bijective"
p2m_open "AlgebraicGeometry"

open IsLocalRing

universe u

theorem Spec_v3genPrime_eq_map_toStalk {A : Type u} [CommRing A] {P Q : PrimeSpectrum A} (h : P ⤳ Q) :
    (Spec (CommRingCat.of A)).v3genPrime h = P.asIdeal.map (StructureSheaf.toStalk A Q).hom := by
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk Q) := StructureSheaf.stalkAlgebra A Q
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk P) := StructureSheaf.stalkAlgebra A P
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk Q) Q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A Q
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk P) P.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A P
  have key := V3Glue.Aux.comap_maximalIdeal_eq_map_of_isLocalization_atPrime Q.asIdeal P.asIdeal
    ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes h).hom (fun a => by
      have h2 := congrArg CommRingCat.Hom.hom (StructureSheaf.toStalk_stalkSpecializes (R := A) h)
      rw [CommRingCat.hom_comp] at h2
      exact RingHom.congr_fun h2 a)
  have halg : (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk Q)) = (StructureSheaf.toStalk A Q).hom :=
    RingHom.ext fun r => rfl
  rw [halg] at key
  exact key

theorem Spec_maximalIdeal_stalk_eq_map_toStalk {A : Type u} [CommRing A] (Q : PrimeSpectrum A) :
    maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk Q) = Q.asIdeal.map (StructureSheaf.toStalk A Q).hom := by
  letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk Q) := StructureSheaf.stalkAlgebra A Q
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk Q) Q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A Q
  have halg : (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk Q)) = (StructureSheaf.toStalk A Q).hom :=
    RingHom.ext fun r => rfl
  rw [← halg]
  exact (IsLocalization.AtPrime.map_eq_maximalIdeal Q.asIdeal ((Spec (CommRingCat.of A)).presheaf.stalk Q)).symm

theorem Spec_v3genPrime_sup_eq_maximalIdeal {A : Type u} [CommRing A] {P₁ P₂ Q : PrimeSpectrum A}
    (h₁ : P₁ ⤳ Q) (h₂ : P₂ ⤳ Q) (hQ : Q.asIdeal = P₁.asIdeal ⊔ P₂.asIdeal) :
    (Spec (CommRingCat.of A)).v3genPrime h₁ ⊔ (Spec (CommRingCat.of A)).v3genPrime h₂ =
      maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk Q) := by
  rw [Spec_v3genPrime_eq_map_toStalk, Spec_v3genPrime_eq_map_toStalk, Spec_maximalIdeal_stalk_eq_map_toStalk, hQ,
    Ideal.map_sup]
  rfl

end AlgebraicGeometry

namespace MvPolynomial
p2m_export "MvPolynomial" "X map R ext induction_on' algebraMap_apply comap algebraMap_eq C monomial C_mul_X_pow_eq_monomial ringHom_ext' CrossingQuotient.Resolution CrossingQuotient.U CrossingQuotient.V CrossingQuotient.U_mul_V CrossingQuotient"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.toCrossing U V U_mul_V lift resolutionChart resolutionChart_U resolutionChart_V mk_surjective monomial ringHom_ext' lineVHom lineUHom lineVHom_U lineVHom_V lineUHom_U lineUHom_V originIdeal lineVIdeal lineUIdeal mem_lineVIdeal_iff mem_lineUIdeal_iff U_notMem_lineVIdeal V_notMem_lineUIdeal algebraMap_mem_lineVIdeal algebraMap_mem_lineUIdeal lineVIdeal_le_originIdeal lineUIdeal_le_originIdeal t_pow_mem branchVPrime branchUPrime one_le originIdeal_eq_span_sup_map lineUIdeal_eq_span_sup_map lineUIdeal_le_iff lineVIdeal_eq_span_sup_map lineVIdeal_le_iff Resolution.origin Resolution.lineGen Resolution.lineUGen Resolution.lineUGen_eq_lineGen Resolution.lineGen_specializes_origin Resolution.lineUGen_specializes_origin Resolution.origin_mem_closure_lineGen Resolution.origin_mem_closure_lineUGen Resolution.vertexPt Resolution.branchVPt Resolution.branchUPt"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq toCrossing origin lineGen lineUGen lineGen_def lineUGen_def lineUGen_eq_lineGen_succ lineUGen_eq_lineGen lineGen_specializes_origin lineUGen_specializes_origin origin_mem_closure_lineGen origin_mem_closure_lineUGen vertexPt branchVPt branchUPt toCrossing_ι_apply eq_origin_of_mem_closure_lineGen_zero eq_origin_of_mem_closure_lineUGen_last"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

p2m_open "AlgebraicGeometry P2MW.S_V3Asm_edgePt_transversal.AlgebraicGeometry IsLocalRing"

universe u

variable {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsPrime] (ht : t ∈ 𝔭)

theorem v3genPrime_lineGen_sup_v3genPrime_lineUGen_eq_maximalIdeal (i : Fin e) :
    (Resolution t e).v3genPrime (lineGen_specializes_origin t e 𝔭 ht i) ⊔
        (Resolution t e).v3genPrime (lineUGen_specializes_origin t e 𝔭 ht i) =
      maximalIdeal ((Resolution t e).presheaf.stalk (origin t e 𝔭 ht i)) := by

  let b : chartScheme t := ⟨originIdeal t 𝔭 ht, inferInstance⟩
  let a₁ : chartScheme t := ⟨lineVIdeal t 𝔭 ht, inferInstance⟩
  let a₂ : chartScheme t := ⟨lineUIdeal t 𝔭 ht, inferInstance⟩
  have h₁ : a₁ ⤳ b := (PrimeSpectrum.le_iff_specializes a₁ b).mp (lineVIdeal_le_originIdeal t 𝔭 ht)
  have h₂ : a₂ ⤳ b := (PrimeSpectrum.le_iff_specializes a₂ b).mp (lineUIdeal_le_originIdeal t 𝔭 ht)
  have hY := Spec_v3genPrime_sup_eq_maximalIdeal h₁ h₂ (originIdeal_eq_lineVIdeal_sup_lineUIdeal t 𝔭 ht)
  exact v3genPrime_sup_genPrime_eq_maximalIdeal_of_stalkMap_bijective (ι t e i) h₁ h₂
    (rfl : ι t e i a₁ = lineGen t e 𝔭 ht i) (rfl : ι t e i a₂ = lineUGen t e 𝔭 ht i) (rfl : ι t e i b = origin t e 𝔭 ht i)
    (lineGen_specializes_origin t e 𝔭 ht i) (lineUGen_specializes_origin t e 𝔭 ht i)
    (IsOpenImmersion.v3_stalkMap_bijective _ _) hY

theorem maximalIdeal_stalk_origin_le_v3genPrime_sup (i : Fin e) :
    maximalIdeal ((Resolution t e).presheaf.stalk (origin t e 𝔭 ht i)) ≤
      (Resolution t e).v3genPrime (lineGen_specializes_origin t e 𝔭 ht i) ⊔
        (Resolution t e).v3genPrime (lineUGen_specializes_origin t e 𝔭 ht i) :=
  (v3genPrime_lineGen_sup_v3genPrime_lineUGen_eq_maximalIdeal t e 𝔭 ht i).ge

theorem maximalIdeal_stalk_origin_le_v3genPrime_sup' (i : Fin e) {μ₁ μ₂ : Resolution t e}
    (e₁ : μ₁ = lineGen t e 𝔭 ht i) (e₂ : μ₂ = lineUGen t e 𝔭 ht i)
    (h₁ : μ₁ ⤳ origin t e 𝔭 ht i) (h₂ : μ₂ ⤳ origin t e 𝔭 ht i) :
    maximalIdeal ((Resolution t e).presheaf.stalk (origin t e 𝔭 ht i)) ≤
      (Resolution t e).v3genPrime h₁ ⊔ (Resolution t e).v3genPrime h₂ := by
  subst e₁ e₂
  exact maximalIdeal_stalk_origin_le_v3genPrime_sup t e 𝔭 ht i

theorem maximalIdeal_stalk_origin_le_v3genPrime_sup'' (i : Fin e) {μ₁ μ₂ : Resolution t e}
    (e₁ : μ₁ = lineUGen t e 𝔭 ht i) (e₂ : μ₂ = lineGen t e 𝔭 ht i)
    (h₁ : μ₁ ⤳ origin t e 𝔭 ht i) (h₂ : μ₂ ⤳ origin t e 𝔭 ht i) :
    maximalIdeal ((Resolution t e).presheaf.stalk (origin t e 𝔭 ht i)) ≤
      (Resolution t e).v3genPrime h₁ ⊔ (Resolution t e).v3genPrime h₂ := by
  rw [sup_comm]
  exact maximalIdeal_stalk_origin_le_v3genPrime_sup' t e 𝔭 ht i e₂ e₁ h₂ h₁

end MvPolynomial.CrossingQuotient.Resolution

end E80ModelTransv

section E80EdgeFullA

namespace V3Asm
p2m_export "V3Asm" "πX bc SiteHyps R C D Y toBase hq mem_X0_iff width hRF p_mem_maximalIdeal ξ ξ_zero ξ_one vertex_eq oRes hoRes gRes hgRes comp η edgePt chainPos'_eq"
p2m_open "V3Asm"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_edgePt_transversal.AlgebraicGeometry IsLocalRing MvPolynomial.CrossingQuotient P2MW.S_V3Asm_edgePt_transversal.MvPolynomial.CrossingQuotient ModularCurve"

section EdgeTransv

variable (p : ℕ) [Fact p.Prime] (𝔛 : ModularCurve.DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (H : V3Asm.SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0)

def EdgeGoal (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n))
    (v w : X0MqComponents (V3Asm.width p 𝔛 O κ toκ hϖ H)) : Prop :=
  ∃ (U : (V3Asm.Y p 𝔛 O κ toκ hϖ H).affineOpens) (hU : V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d ∈ (U : (V3Asm.Y p 𝔛 O κ toκ hϖ H).Opens)),
    Ideal.map ((V3Asm.Y p 𝔛 O κ toκ hϖ H).presheaf.germ (U : (V3Asm.Y p 𝔛 O κ toκ hϖ H).Opens) (V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d) hU).hom
        ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ v).ideal U ⊔ (V3Asm.comp p 𝔛 O κ toκ hϖ H hξ w).ideal U) =
      IsLocalRing.maximalIdeal ((V3Asm.Y p 𝔛 O κ toκ hϖ H).presheaf.stalk (V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d))

theorem edgeGoal_of_witnesses (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n))
    (v w : X0MqComponents (V3Asm.width p 𝔛 O κ toκ hϖ H))
    (a₁ a₂ : (V3Asm.C p 𝔛 O κ toκ hϖ H).Y n)
    (ha₁ : (V3Asm.C p 𝔛 O κ toκ hϖ H).toGlueInput.ιY n a₁ = V3Asm.η p 𝔛 O κ toκ hϖ H hξ v)
    (ha₂ : (V3Asm.C p 𝔛 O κ toκ hϖ H).toGlueInput.ιY n a₂ = V3Asm.η p 𝔛 O κ toκ hϖ H hξ w)
    (h₁ : a₁ ⤳ (V3Asm.C p 𝔛 O κ toκ hϖ H).liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d))
    (h₂ : a₂ ⤳ (V3Asm.C p 𝔛 O κ toκ hϖ H).liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d))
    (e₁ : (V3Asm.C p 𝔛 O κ toκ hϖ H).g n a₁ = Resolution.lineGen ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) d)
    (e₂ : (V3Asm.C p 𝔛 O κ toκ hϖ H).g n a₂ = Resolution.lineUGen ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) d) :
    EdgeGoal p 𝔛 O hϖ κ toκ H hξ n d v w := by
  let C := V3Asm.C p 𝔛 O κ toκ hϖ H
  let t : O := ((p : ℕ) : O)
  let e : ℕ := C.thick n
  have ht : t ∈ IsLocalRing.maximalIdeal O := V3Asm.p_mem_maximalIdeal p O hϖ
  have hod : V3Asm.oRes p 𝔛 O κ toκ hϖ H n d = Resolution.origin t e (IsLocalRing.maximalIdeal O) ht d := rfl
  have hμ₁ : Resolution.lineGen t e (IsLocalRing.maximalIdeal O) ht d ⤳ V3Asm.oRes p 𝔛 O κ toκ hϖ H n d :=
    Resolution.lineGen_specializes_origin t e _ ht d
  have hμ₂ : Resolution.lineUGen t e (IsLocalRing.maximalIdeal O) ht d ⤳ V3Asm.oRes p 𝔛 O κ toκ hϖ H n d :=
    Resolution.lineUGen_specializes_origin t e _ ht d
  haveI : Etale (C.g n) := MorphismProperty.pullback_snd _ _ inferInstance
  have hmax := V3Glue.Aux.Etale.map_stalkMap_maximalIdeal (C.g n)
    (C.liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d))
  have hM4 : maximalIdeal ((C.Res n).presheaf.stalk (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d)) ≤
      (C.Res n).v3genPrime hμ₁ ⊔ (C.Res n).v3genPrime hμ₂ :=
    Resolution.maximalIdeal_stalk_origin_le_v3genPrime_sup t e (IsLocalRing.maximalIdeal O) ht d
  exact C.edgePt'_transversal (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H)
    (V3Asm.ξ p 𝔛 O κ toκ) hξ (V3Asm.oRes p 𝔛 O κ toκ hϖ H) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H) n d v w a₁ a₂ ha₁ ha₂ h₁ h₂
    _ _ e₁ e₂ hμ₁ hμ₂ hmax hM4

theorem excWitness_lo (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n))
    (k : Fin (V3Asm.width p 𝔛 O κ toκ hϖ H n - 1)) (hk : (d : ℕ) = (k : ℕ) + 1) :
    ∃ a : (V3Asm.C p 𝔛 O κ toκ hϖ H).Y n,
      (V3Asm.C p 𝔛 O κ toκ hϖ H).toGlueInput.ιY n a = V3Asm.η p 𝔛 O κ toκ hϖ H hξ (Sum.inr ⟨n, k⟩) ∧
      a ⤳ (V3Asm.C p 𝔛 O κ toκ hϖ H).liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d) ∧
      (V3Asm.C p 𝔛 O κ toκ hϖ H).g n a = Resolution.lineGen ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)
        (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) d := by
  let C := V3Asm.C p 𝔛 O κ toκ hϖ H
  let t : O := ((p : ℕ) : O)
  have ht : t ∈ IsLocalRing.maximalIdeal O := V3Asm.p_mem_maximalIdeal p O hϖ
  have eg : V3Asm.gRes p 𝔛 O κ toκ hϖ H n k = Resolution.lineGen t (C.thick n) (IsLocalRing.maximalIdeal O) ht d := by
    show Resolution.lineUGen t (C.thick n) (IsLocalRing.maximalIdeal O) _ ⟨(k : ℕ), _⟩ = _
    exact Resolution.lineUGen_eq_lineGen t (C.thick n) (IsLocalRing.maximalIdeal O) _ hk
  have hcl : V3Asm.oRes p 𝔛 O κ toκ hϖ H n d ∈ closure ({V3Asm.gRes p 𝔛 O κ toκ hϖ H n k} : Set (C.Res n)) := by
    rw [eg]; exact Resolution.origin_mem_closure_lineGen t (C.thick n) (IsLocalRing.maximalIdeal O) ht d
  refine ⟨C.liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.gRes p 𝔛 O κ toκ hϖ H n k) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H n k),
    rfl, C.liftY_specializes_liftY n _ _ _ _ _ hcl, ?_⟩
  rw [C.g_liftY]; exact eg

theorem excWitness_hi (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n))
    (k : Fin (V3Asm.width p 𝔛 O κ toκ hϖ H n - 1)) (hk : (k : ℕ) = (d : ℕ)) :
    ∃ a : (V3Asm.C p 𝔛 O κ toκ hϖ H).Y n,
      (V3Asm.C p 𝔛 O κ toκ hϖ H).toGlueInput.ιY n a = V3Asm.η p 𝔛 O κ toκ hϖ H hξ (Sum.inr ⟨n, k⟩) ∧
      a ⤳ (V3Asm.C p 𝔛 O κ toκ hϖ H).liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d) ∧
      (V3Asm.C p 𝔛 O κ toκ hϖ H).g n a = Resolution.lineUGen ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)
        (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) d := by
  let C := V3Asm.C p 𝔛 O κ toκ hϖ H
  let t : O := ((p : ℕ) : O)
  have ht : t ∈ IsLocalRing.maximalIdeal O := V3Asm.p_mem_maximalIdeal p O hϖ
  have eg : V3Asm.gRes p 𝔛 O κ toκ hϖ H n k = Resolution.lineUGen t (C.thick n) (IsLocalRing.maximalIdeal O) ht d := by
    show Resolution.lineUGen t (C.thick n) (IsLocalRing.maximalIdeal O) _ ⟨(k : ℕ), _⟩ = _
    congr 1; exact Fin.ext hk
  have hcl : V3Asm.oRes p 𝔛 O κ toκ hϖ H n d ∈ closure ({V3Asm.gRes p 𝔛 O κ toκ hϖ H n k} : Set (C.Res n)) := by
    rw [eg]; exact Resolution.origin_mem_closure_lineUGen t (C.thick n) (IsLocalRing.maximalIdeal O) ht d
  refine ⟨C.liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.gRes p 𝔛 O κ toκ hϖ H n k) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H n k),
    rfl, C.liftY_specializes_liftY n _ _ _ _ _ hcl, ?_⟩
  rw [C.g_liftY]; exact eg

theorem strictWitness_zero (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n)) (hd : (d : ℕ) = 0)
    (horient : ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, V3Asm.ξ_mem_U p 𝔛 O hϖ κ toκ H n 0⟩ =
      Resolution.branchVPt ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O)
        (V3Asm.p_mem_maximalIdeal p O hϖ) ((V3Asm.C p 𝔛 O κ toκ hϖ H).one_le_thick n)) :
    ∃ a : (V3Asm.C p 𝔛 O κ toκ hϖ H).Y n,
      (V3Asm.C p 𝔛 O κ toκ hϖ H).toGlueInput.ιY n a = V3Asm.η p 𝔛 O κ toκ hϖ H hξ (Sum.inl 0) ∧
      a ⤳ (V3Asm.C p 𝔛 O κ toκ hϖ H).liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d) ∧
      (V3Asm.C p 𝔛 O κ toκ hϖ H).g n a = Resolution.lineGen ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)
        (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) d := by
  let C := V3Asm.C p 𝔛 O κ toκ hϖ H
  let t : O := ((p : ℕ) : O)
  let e : ℕ := C.thick n
  have he : 1 ≤ e := C.one_le_thick n
  have ht : t ∈ IsLocalRing.maximalIdeal O := V3Asm.p_mem_maximalIdeal p O hϖ
  haveI : (IsLocalRing.maximalIdeal O).IsMaximal := IsLocalRing.maximalIdeal.isMaximal O
  have hU := V3Asm.ξ_mem_U p 𝔛 O hϖ κ toκ H n 0
  have hxcl := V3Asm.xU_mem_closure_ξ p 𝔛 O hϖ κ toκ H n 0
  have hd' : (⟨0, he⟩ : Fin e) = d := Fin.ext hd.symm
  let a : C.Y n := C.ξY (V3Asm.ξ p 𝔛 O κ toκ) hξ n 0 hU

  have hga : (C.ρ n) (C.g n a) = Resolution.branchVPt t e (IsLocalRing.maximalIdeal O) ht he := by
    rw [← Scheme.Hom.comp_apply, ← C.q_f, Scheme.Hom.comp_apply]
    have hq : C.q n a = ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩ := C.q_ξY (V3Asm.ξ p 𝔛 O κ toκ) hξ n 0 hU
    rw [hq]; exact horient
  have e₁ : C.g n a = Resolution.lineGen t e (IsLocalRing.maximalIdeal O) ht d := by
    rw [← hd']; exact Resolution.eq_lineGen_zero_of_toCrossing_eq_branchVPt t _ ht e he _ hga

  have hvert := V3Asm.vertex_eq p 𝔛 O κ toκ hϖ H n
  have hspec : ∀ o o' : C.Res n, C.ρ n o = C.f n ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU⟩ → o' ∈ closure ({o} : Set (C.Res n)) →
      C.ρ n o' = C.vertex n → o' = V3Asm.oRes p 𝔛 O κ toκ hϖ H n d := by
    intro o o' ho ho' hv
    have ho2 : Resolution.toCrossing t e o = Resolution.branchVPt t e (IsLocalRing.maximalIdeal O) ht he := by
      show (C.ρ n) o = _; rw [ho]; exact horient
    have hv2 : Resolution.toCrossing t e o' = Resolution.vertexPt t e (IsLocalRing.maximalIdeal O) ht he := by
      show (C.ρ n) o' = _; rw [hv]; exact hvert
    have := Resolution.eq_origin_zero_of_mem_closure_of_toCrossing_eq_branchVPt t _ ht e he o o' ho2 ho' hv2
    rw [this]; show Resolution.origin t e (IsLocalRing.maximalIdeal O) ht ⟨0, he⟩ = Resolution.origin t e (IsLocalRing.maximalIdeal O) _ d
    rw [hd']
  refine ⟨a, C.ιY_ξY (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) _ hξ n 0 hU, ?_, e₁⟩
  exact C.ξY_specializes_liftY (hRF := V3Asm.hRF p 𝔛 O κ toκ hϖ H) (ξ := V3Asm.ξ p 𝔛 O κ toκ) (hξ := hξ)
    (oRes := V3Asm.oRes p 𝔛 O κ toκ hϖ H) (hoRes := V3Asm.hoRes p 𝔛 O κ toκ hϖ H) n 0 d hU hxcl hspec

theorem strictWitness_one (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n))
    (hd : (d : ℕ) + 1 = V3Asm.width p 𝔛 O κ toκ hϖ H n)
    (horient : ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, V3Asm.ξ_mem_U p 𝔛 O hϖ κ toκ H n 1⟩ =
      Resolution.branchUPt ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O)
        (V3Asm.p_mem_maximalIdeal p O hϖ) ((V3Asm.C p 𝔛 O κ toκ hϖ H).one_le_thick n)) :
    ∃ a : (V3Asm.C p 𝔛 O κ toκ hϖ H).Y n,
      (V3Asm.C p 𝔛 O κ toκ hϖ H).toGlueInput.ιY n a = V3Asm.η p 𝔛 O κ toκ hϖ H hξ (Sum.inl 1) ∧
      a ⤳ (V3Asm.C p 𝔛 O κ toκ hϖ H).liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d) ∧
      (V3Asm.C p 𝔛 O κ toκ hϖ H).g n a = Resolution.lineUGen ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)
        (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) d := by
  let C := V3Asm.C p 𝔛 O κ toκ hϖ H
  let t : O := ((p : ℕ) : O)
  let e : ℕ := C.thick n
  have he : 1 ≤ e := C.one_le_thick n
  have ht : t ∈ IsLocalRing.maximalIdeal O := V3Asm.p_mem_maximalIdeal p O hϖ
  haveI : (IsLocalRing.maximalIdeal O).IsMaximal := IsLocalRing.maximalIdeal.isMaximal O
  have hU := V3Asm.ξ_mem_U p 𝔛 O hϖ κ toκ H n 1
  have hxcl := V3Asm.xU_mem_closure_ξ p 𝔛 O hϖ κ toκ H n 1
  have hwt : V3Asm.width p 𝔛 O κ toκ hϖ H n = e := rfl
  have hd' : (⟨e - 1, by omega⟩ : Fin e) = d := Fin.ext (by simp only [Fin.val_mk]; omega)
  let a : C.Y n := C.ξY (V3Asm.ξ p 𝔛 O κ toκ) hξ n 1 hU
  have hga : (C.ρ n) (C.g n a) = Resolution.branchUPt t e (IsLocalRing.maximalIdeal O) ht he := by
    rw [← Scheme.Hom.comp_apply, ← C.q_f, Scheme.Hom.comp_apply]
    have hq : C.q n a = ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩ := C.q_ξY (V3Asm.ξ p 𝔛 O κ toκ) hξ n 1 hU
    rw [hq]; exact horient
  have e₁ : C.g n a = Resolution.lineUGen t e (IsLocalRing.maximalIdeal O) ht d := by
    rw [← hd']; exact Resolution.eq_lineUGen_last_of_toCrossing_eq_branchUPt t _ ht e he _ hga
  have hvert := V3Asm.vertex_eq p 𝔛 O κ toκ hϖ H n
  have hspec : ∀ o o' : C.Res n, C.ρ n o = C.f n ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU⟩ → o' ∈ closure ({o} : Set (C.Res n)) →
      C.ρ n o' = C.vertex n → o' = V3Asm.oRes p 𝔛 O κ toκ hϖ H n d := by
    intro o o' ho ho' hv
    have ho2 : Resolution.toCrossing t e o = Resolution.branchUPt t e (IsLocalRing.maximalIdeal O) ht he := by
      show (C.ρ n) o = _; rw [ho]; exact horient
    have hv2 : Resolution.toCrossing t e o' = Resolution.vertexPt t e (IsLocalRing.maximalIdeal O) ht he := by
      show (C.ρ n) o' = _; rw [hv]; exact hvert
    have := Resolution.eq_origin_last_of_mem_closure_of_toCrossing_eq_branchUPt t _ ht e he o o' ho2 ho' hv2
    rw [this]; show Resolution.origin t e (IsLocalRing.maximalIdeal O) ht ⟨e - 1, _⟩ = Resolution.origin t e (IsLocalRing.maximalIdeal O) _ d
    rw [hd']
  refine ⟨a, C.ιY_ξY (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) _ hξ n 1 hU, ?_, e₁⟩
  exact C.ξY_specializes_liftY (hRF := V3Asm.hRF p 𝔛 O κ toκ hϖ H) (ξ := V3Asm.ξ p 𝔛 O κ toκ) (hξ := hξ)
    (oRes := V3Asm.oRes p 𝔛 O κ toκ hϖ H) (hoRes := V3Asm.hoRes p 𝔛 O κ toκ hϖ H) n 1 d hU hxcl hspec

theorem edgePt_transversal_of_orient
    (horient0 : ∀ n : V3Glue.Site.Node p 𝔛 κ, ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, V3Asm.ξ_mem_U p 𝔛 O hϖ κ toκ H n 0⟩ =
      Resolution.branchVPt ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O)
        (V3Asm.p_mem_maximalIdeal p O hϖ) ((V3Asm.C p 𝔛 O κ toκ hϖ H).one_le_thick n))
    (horient1 : ∀ n : V3Glue.Site.Node p 𝔛 κ, ((V3Asm.C p 𝔛 O κ toκ hϖ H).f n).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, V3Asm.ξ_mem_U p 𝔛 O hϖ κ toκ H n 1⟩ =
      Resolution.branchUPt ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O)
        (V3Asm.p_mem_maximalIdeal p O hϖ) ((V3Asm.C p 𝔛 O κ toκ hϖ H).one_le_thick n))
    (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n)) :
    EdgeGoal p 𝔛 O hϖ κ toκ H hξ n d
      (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n d)
      (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n ((d : ℕ) + 1)) := by
  let C := V3Asm.C p 𝔛 O κ toκ hϖ H
  have hdlt : (d : ℕ) < V3Asm.width p 𝔛 O κ toκ hϖ H n := d.2

  obtain ⟨a₁, ha₁, h₁, e₁⟩ : ∃ a : C.Y n, C.toGlueInput.ιY n a =
      V3Asm.η p 𝔛 O κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n d) ∧
      a ⤳ C.liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d) ∧
      C.g n a = Resolution.lineGen ((p : ℕ) : O) (C.thick n) (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) d := by
    rcases Nat.eq_zero_or_pos (d : ℕ) with hd0 | hdpos
    · rw [← V3Asm.chainPos'_eq, hd0, C.chainPos'_zero]
      exact strictWitness_zero p 𝔛 O hϖ κ toκ H hξ n d hd0 (horient0 n)
    · let k : Fin (V3Asm.width p 𝔛 O κ toκ hϖ H n - 1) := ⟨(d : ℕ) - 1, by omega⟩
      have hk : (d : ℕ) = (k : ℕ) + 1 := by simp only [k]; omega
      rw [← V3Asm.chainPos'_eq, hk, C.chainPos'_succ n k]
      exact excWitness_lo p 𝔛 O hϖ κ toκ H hξ n d k hk

  obtain ⟨a₂, ha₂, h₂, e₂⟩ : ∃ a : C.Y n, C.toGlueInput.ιY n a =
      V3Asm.η p 𝔛 O κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n ((d : ℕ) + 1)) ∧
      a ⤳ C.liftY n (V3Asm.hRF p 𝔛 O κ toκ hϖ H n) (V3Asm.oRes p 𝔛 O κ toκ hϖ H n d) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H n d) ∧
      C.g n a = Resolution.lineUGen ((p : ℕ) : O) (C.thick n) (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) d := by
    by_cases hlast : (d : ℕ) + 1 = V3Asm.width p 𝔛 O κ toκ hϖ H n
    · rw [← V3Asm.chainPos'_eq, C.chainPos'_of_le n _ hlast.ge]
      exact strictWitness_one p 𝔛 O hϖ κ toκ H hξ n d hlast (horient1 n)
    · let k : Fin (V3Asm.width p 𝔛 O κ toκ hϖ H n - 1) := ⟨(d : ℕ), by omega⟩
      rw [← V3Asm.chainPos'_eq, C.chainPos'_succ n k]
      exact excWitness_hi p 𝔛 O hϖ κ toκ H hξ n d k rfl
  exact edgeGoal_of_witnesses p 𝔛 O hϖ κ toκ H hξ n d _ _ a₁ a₂ ha₁ ha₂ h₁ h₂ e₁ e₂

end EdgeTransv

end V3Asm

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_V3Asm_edgePt_transversal.AlgebraicGeometry in

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : ModularCurve.DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (H : V3Asm.SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) :
    ∀ (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n)), ∃ (U : (V3Asm.Y p 𝔛 O κ toκ hϖ H).affineOpens) (hU : V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d ∈ (U : (V3Asm.Y p 𝔛 O κ toκ hϖ H).Opens)),
      Ideal.map ((V3Asm.Y p 𝔛 O κ toκ hϖ H).presheaf.germ (U : (V3Asm.Y p 𝔛 O κ toκ hϖ H).Opens) (V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d) hU).hom
          ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n d)).ideal U ⊔ (V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n (d + 1))).ideal U) =
        IsLocalRing.maximalIdeal ((V3Asm.Y p 𝔛 O κ toκ hϖ H).presheaf.stalk (V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d)) := by
  intro n d
  exact V3Asm.edgePt_transversal_of_orient p 𝔛 O hϖ κ toκ H hξ
    (horient0 := fun n => V3Asm.f_ξ_zero_eq_branchVPt (p := p) (𝔛 := 𝔛) (O := O) (hϖ := hϖ) (κ := κ) (toκ := toκ) (H := H) n _)
    (horient1 := fun n => V3Asm.f_ξ_one_eq_branchUPt (p := p) (𝔛 := 𝔛) (O := O) (hϖ := hϖ) (κ := κ) (toκ := toκ) (H := H) n _) n d

end E80EdgeFullA

end S_V3Asm_edgePt_transversal
end P2MW
export P2MW.S_V3Asm_edgePt_transversal (solution)
