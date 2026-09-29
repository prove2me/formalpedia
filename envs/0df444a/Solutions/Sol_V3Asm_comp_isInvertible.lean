-- Prove2me | solution 1 for V3Asm.comp_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ab576b7e-d6eb-528b-8357-ff247540855c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_ModularCurve_DRResolvedModelCharts
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_MvPolynomial_CrossingQuotient
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_Mathlib_RingTheory_RegularLocalRingFlatLocalAscentV2
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isProper_toCrossing
import Theorems.Thm_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top
import Theorems.Thm_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing
import Theorems.Thm_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_mem_preimage_smoothLocus
import Theorems.Thm_ModularCurve_DRModel_isIntegral_pullback_toBase
import Theorems.Thm_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
import Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_idealSheafData_chartTable
import Theorems.Thm_ModularCurve_DRModelPackage_isRegularLocalRing_stalk_of_forall_ne_baseChangeMap_crossing
import Theorems.Thm_ModularCurve_DRModelPackage_ringKrullDim_stalk_pullback_toBase_le_two
import Definitions.Def_ModularCurve_ResolvedModelSite
import Theorems.Thm_V3Glue_ChartInput_isReduced_Y
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
import Theorems.Thm_ModularCurve_DRModelPackage_eq_baseChangeMap_genericPoint_of_specializes
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_vanishingIdeal_closure_of_isRegularLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Asm_comp_isInvertible
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false
set_option maxHeartbeats 800000

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient"

namespace MvPolynomial
p2m_export "MvPolynomial" "comap_comp X map constantCoeff R ringKrullDim_of_isNoetherianRing ext support comap coe_add vanishingIdeal C rTensor monomial coe_one induction_on CrossingQuotient.Resolution CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient CrossingQuotient.isRegularRing_of_irreducible CrossingQuotient.Resolution.isRegularLocalRing_stalk CrossingQuotient.lineUIdeal CrossingQuotient.algebraMap_mem_span_U CrossingQuotient.lineUIdeal_eq_span_sup_map CrossingQuotient.Resolution.lineUGen CrossingQuotient.Resolution.origin_injective CrossingQuotient.Resolution.lineUGen_injective CrossingQuotient.Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme chartScheme Resolution Resolution.ι Resolution.exists_ι_apply_eq Resolution.toSpec U V U_mul_V resolutionChart resolutionChart_U resolutionChart_V mk monomial linearIndependent_monomial_and_span_eq_top isRegularRing_of_irreducible Resolution.isRegularLocalRing_stalk lineUIdeal algebraMap_mem_span_U lineUIdeal_eq_span_sup_map Resolution.lineUGen Resolution.origin_injective Resolution.lineUGen_injective Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen"
p2m_open "MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W)

noncomputable def monomialBasis : Module.Basis ℤ W (CrossingQuotient W t) :=
  Module.Basis.mk (linearIndependent_monomial_and_span_eq_top t).1
    (linearIndependent_monomial_and_span_eq_top t).2.ge

scoped instance free : Module.Free W (CrossingQuotient W t) := Module.Free.of_basis (monomialBasis t)

theorem flat_algebraMap : (algebraMap W (CrossingQuotient W t)).Flat := by
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

theorem mem_nonZeroDivisors_map_of_flat {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : φ.Flat) {r : R} (hr : r ∈ nonZeroDivisors R) : φ r ∈ nonZeroDivisors S := by
  letI := φ.toAlgebra
  have hflat : Module.Flat R S := hφ
  have hsm : IsSMulRegular S r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x : S, φ r * x = 0 → x = 0 := fun x hx =>
    hsm ((Algebra.smul_def r x).trans (hx.trans (smul_zero r).symm))
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx => key x ((mul_comm _ _).trans hx)⟩

theorem algebraMap_mem_nonZeroDivisors {s : W} (hs : s ∈ nonZeroDivisors W) :
    algebraMap W (CrossingQuotient W t) s ∈ nonZeroDivisors (CrossingQuotient W t) :=
  mem_nonZeroDivisors_map_of_flat (flat_algebraMap t) hs

theorem interior_setOf_mem_asIdeal_eq_empty {A : Type u} [CommRing A] {s : A} (hs : s ∈ nonZeroDivisors A) :
    interior {P : PrimeSpectrum A | s ∈ P.asIdeal} = ∅ := by
  rw [← Set.subset_empty_iff]
  intro P hP
  obtain ⟨_, ⟨g, rfl⟩, hPg, hg⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP isOpen_interior
  have hsub : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆ {P | s ∈ P.asIdeal} :=
    hg.trans interior_subset
  have hempty : PrimeSpectrum.basicOpen (g * s) = ⊥ := by
    rw [PrimeSpectrum.basicOpen_mul, eq_bot_iff]
    intro Q hQ
    exact (hQ.2 (hsub hQ.1)).elim
  rw [PrimeSpectrum.basicOpen_eq_bot_iff] at hempty
  obtain ⟨n, hn⟩ := hempty
  rw [mul_pow, mul_comm] at hn
  have hgn : g ^ n = 0 := (mem_nonZeroDivisors_iff.mp ((nonZeroDivisors A).pow_mem hs n)).1 _ hn
  exact hPg (P.2.mem_of_pow_mem n (hgn ▸ P.asIdeal.zero_mem))

namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq openCover chartToCrossing toCrossing ι_toCrossing toSpec ι_toSpec isRegularLocalRing_stalk lineGen lineUGen origin_injective lineUGen_injective eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen"
p2m_open "MvPolynomial.CrossingQuotient.Resolution"

variable (e : ℕ)

theorem flat_toCrossing_comp_Spec_map :
    Flat (toCrossing t e ≫ Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W (t ^ e))))) := by
  refine IsZariskiLocalAtSource.of_openCover (openCover t e) fun i => ?_
  show Flat (ι t e i ≫ toSpec t e)
  rw [ι_toSpec]
  exact HasRingHomProperty.Spec_iff.mpr (flat_algebraMap t)

theorem flat_toSpec : Flat (toSpec t e) := flat_toCrossing_comp_Spec_map t e

private theorem _root_.MvPolynomial.CrossingQuotient.Resolution.isLocallyNoetherian [IsNoetherianRing W] : IsLocallyNoetherian (Resolution t e) := by
  rw [isLocallyNoetherian_iff_openCover (openCover t e)]
  intro i
  show IsLocallyNoetherian (chartScheme t)
  infer_instance

p2m_export "MvPolynomial.CrossingQuotient.Resolution" "isLocallyNoetherian"

theorem algebraMap_mem_asIdeal_of_ι_notMem (i : Fin e) (y : chartScheme t)
    (hy : toCrossing t e (ι t e i y) ∉
      (PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)) :
        (crossingScheme (t ^ e)).Opens)) :
    algebraMap W (CrossingQuotient W t) t ∈ y.asIdeal := by
  rw [← Scheme.Hom.comp_apply, ι_toCrossing] at hy
  have hU : resolutionChart t e i (U (t ^ e)) ∈ y.asIdeal := by
    by_contra h
    exact hy ((le_sup_left : PrimeSpectrum.basicOpen (U (t ^ e)) ≤
      (PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)) : (crossingScheme (t ^ e)).Opens))
      (show (chartToCrossing t e i) y ∈ (PrimeSpectrum.basicOpen (U (t ^ e)) : (crossingScheme (t ^ e)).Opens) from h))
  have hV : resolutionChart t e i (V (t ^ e)) ∈ y.asIdeal := by
    by_contra h
    exact hy ((le_sup_right : PrimeSpectrum.basicOpen (V (t ^ e)) ≤
      (PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)) : (crossingScheme (t ^ e)).Opens))
      (show (chartToCrossing t e i) y ∈ (PrimeSpectrum.basicOpen (V (t ^ e)) : (crossingScheme (t ^ e)).Opens) from h))
  rw [resolutionChart_U] at hU
  rw [resolutionChart_V] at hV
  have hi : (i : ℕ) + (e - 1 - i) + 1 = e := by have := i.2; omega
  have hte : algebraMap W (CrossingQuotient W t) (t ^ e) ∈ y.asIdeal := by
    have h := y.asIdeal.mul_mem_left (algebraMap W _ (t ^ (i : ℕ)) * U t) hV
    rwa [mul_mul_mul_comm, U_mul_V, ← map_mul, ← map_mul, ← pow_add, ← pow_succ, hi] at h
  rw [map_pow] at hte
  exact y.2.mem_of_pow_mem e hte

theorem interior_preimage_vertex_eq_empty (ht : t ∈ nonZeroDivisors W) :
    interior ((toCrossing t e).base ⁻¹'
      ((PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)) :
        (crossingScheme (t ^ e)).Opens) : Set (crossingScheme (t ^ e)))ᶜ) = ∅ := by
  rw [← Set.subset_empty_iff]
  intro x hx
  obtain ⟨i, y, rfl⟩ := exists_ι_apply_eq t e x
  have hopen : IsOpen ((ι t e i).base ⁻¹' interior ((toCrossing t e).base ⁻¹'
      ((PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)) :
        (crossingScheme (t ^ e)).Opens) : Set (crossingScheme (t ^ e)))ᶜ)) :=
    isOpen_interior.preimage (ι t e i).continuous
  have hsub : (ι t e i).base ⁻¹' interior ((toCrossing t e).base ⁻¹'
      ((PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)) :
        (crossingScheme (t ^ e)).Opens) : Set (crossingScheme (t ^ e)))ᶜ) ⊆
      {P : PrimeSpectrum (CrossingQuotient W t) | algebraMap W (CrossingQuotient W t) t ∈ P.asIdeal} :=
    fun z hz => algebraMap_mem_asIdeal_of_ι_notMem t e i z (interior_subset hz)
  have hy : y ∈ interior {P : PrimeSpectrum (CrossingQuotient W t) |
      algebraMap W (CrossingQuotient W t) t ∈ P.asIdeal} := interior_maximal hsub hopen hx
  rw [interior_setOf_mem_asIdeal_eq_empty (algebraMap_mem_nonZeroDivisors t ht)] at hy
  exact hy

end Resolution

end MvPolynomial.CrossingQuotient
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial"

namespace MvPolynomial p2m_export "MvPolynomial" "comap_comp X map constantCoeff R ringKrullDim_of_isNoetherianRing ext support comap coe_add vanishingIdeal C rTensor monomial coe_one induction_on CrossingQuotient.Resolution CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient CrossingQuotient.isRegularRing_of_irreducible CrossingQuotient.Resolution.isRegularLocalRing_stalk CrossingQuotient.lineUIdeal CrossingQuotient.algebraMap_mem_span_U CrossingQuotient.lineUIdeal_eq_span_sup_map CrossingQuotient.Resolution.lineUGen CrossingQuotient.Resolution.origin_injective CrossingQuotient.Resolution.lineUGen_injective CrossingQuotient.Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen" namespace CrossingQuotient p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme chartScheme Resolution Resolution.ι Resolution.exists_ι_apply_eq Resolution.toSpec U V U_mul_V resolutionChart resolutionChart_U resolutionChart_V mk monomial linearIndependent_monomial_and_span_eq_top isRegularRing_of_irreducible Resolution.isRegularLocalRing_stalk lineUIdeal algebraMap_mem_span_U lineUIdeal_eq_span_sup_map Resolution.lineUGen Resolution.origin_injective Resolution.lineUGen_injective Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen" namespace Resolution p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq openCover chartToCrossing toCrossing ι_toCrossing toSpec ι_toSpec isRegularLocalRing_stalk lineGen lineUGen origin_injective lineUGen_injective eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen" end MvPolynomial.CrossingQuotient.Resolution
p2m_open_scoped "MvPolynomial MvPolynomial.CrossingQuotient MvPolynomial.CrossingQuotient.Resolution" in

theorem MvPolynomial.CrossingQuotient.Resolution.isReduced {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) : AlgebraicGeometry.IsReduced (Resolution ϖ e) := by
  haveI : ∀ x : Resolution ϖ e, _root_.IsReduced ((Resolution ϖ e).presheaf.stalk x) := fun x =>
    haveI := Resolution.isRegularLocalRing_stalk hϖ e x
    haveI := IsRegularLocalRing.isDomain ((Resolution ϖ e).presheaf.stalk x)
    inferInstance
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

noncomputable section
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian LocallyOfFiniteType.stalkMap IsProper basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsZariskiLocalAtSource.of_openCover stalkwise FormallyUnramified.stalkMap Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth Scheme.IdealSheafData.vanishingIdeal isReduced_of_isIntegral isReduced_of_isReduced_stalk IsZariskiLocalAtSource IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isLocallyNoetherian_iff_openCover Flat.stalkMap Flat IsReduced HasRingHomProperty.Spec_iff isAffineOpen_top Scheme.preimage_basicOpen_top Etale IsAffineOpen IsNoetherian FormallyUnramified Flat.generalizingMap isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Hom.comp_apply basicOpen_eq_of_affine Scheme.IdealSheafData Scheme.ΓSpecIso v3_isReduced_pullback_subschemeι_of_isOpenImmersion Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing Smooth.isReduced_of_isReduced_of_isLocallyNoetherian Scheme.isIntegral_subscheme_vanishingIdeal Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen fromSpecResidueField Hom mk Γ empty preimage_basicOpen IdealSheafData.vanishingIdeal basicOpen_zero Hom.comp_base residueField affineOpens basicOpen preimage_basicOpen_top basicOpen_mul Opens residue homOfLE_ι le_iff_specializes restrict Hom.comp_apply IdealSheafData ΓSpecIso isIntegral_subscheme_vanishingIdeal ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "radical support_comap comap_comp mk map subscheme vanishingIdeal comap_top vanishingIdeal_ideal ideal support_eq_bot_iff subschemeι comap subschemeCover ofIdealTop support ofIdealTop_ideal v3_comap_eq_vanishingIdeal_of_isReduced IsInvertible comap_mul prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup eq_of_forall_comap_openCover_eq comap_ofIdealTop isInvertible_vanishingIdeal_closure_of_isRegularLocalRing"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq"

open TopologicalSpace

scoped instance isReduced_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  haveI hq : ∀ U : X.affineOpens, _root_.IsReduced (Γ(X, U) ⧸ (vanishingIdeal Z).ideal U) := fun U => by
    rw [← Ideal.isRadical_iff_quotient_reduced, vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  haveI : ∀ U : X.affineOpens, IsReduced ((vanishingIdeal Z).subschemeCover.openCover.X U) := fun U =>
    inferInstanceAs (IsReduced (Spec (.of (Γ(X, U) ⧸ (vanishingIdeal Z).ideal U))))
  exact IsReduced.of_openCover _ (vanishingIdeal Z).subschemeCover.openCover

theorem comap_vanishingIdeal_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (Z : Closeds Y) :
    (vanishingIdeal Z).comap f = vanishingIdeal ⟨f.base ⁻¹' (Z : Set Y), Z.isClosed.preimage f.continuous⟩ := by
  haveI := v3_isReduced_pullback_subschemeι_of_isOpenImmersion f (vanishingIdeal Z)
  exact (v3_comap_eq_vanishingIdeal_of_isReduced (vanishingIdeal Z) f).trans rfl

theorem comap_finset_prod {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [comap_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, comap_mul, ih]

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry"

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

private theorem _root_.V3Glue.ChartInput.comap_ιX0_compG_inr (hx : ∀ n, IsClosed ({C.x n} : Set X)) (n : N) (k : Fin (C.thick n - 1)) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).comap C.toGlueInput.ιX0 = ⊤ := by
  rw [← support_eq_bot_iff, support_comap]
  ext y0
  simp only [Closeds.coe_preimage, Set.mem_preimage, Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hy
  have h1 := C.exc_image' hRF gRes hgRes ξ hξ hx n k _ hy
  have h2 : C.toGlueInput.toDR (C.toGlueInput.ιX0 y0) = y0.1 := by
    rw [← Scheme.Hom.comp_apply, C.toGlueInput.ιX0_toDR]; rfl
  rw [h2] at h1
  exact ((C.mem_X0 _).mp y0.2) n h1

p2m_export "V3Glue.ChartInput" "comap_ιX0_compG_inr"

private theorem _root_.V3Glue.ChartInput.comap_ιX0_compG_inl (j : Fin 2) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).comap C.toGlueInput.ιX0 =
      vanishingIdeal ⟨closure ({(⟨ξ j, hξ j⟩ : C.X0)} : Set C.X0), isClosed_closure⟩ := by
  rw [compG, comap_vanishingIdeal_of_isOpenImmersion]
  congr 1
  ext1
  change C.toGlueInput.ιX0.base ⁻¹' closure {C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)} = closure {(⟨ξ j, hξ j⟩ : C.X0)}
  rw [ηG_inl, C.toGlueInput.ιX0.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    C.toGlueInput.ιX0.continuous]
  congr 1
  ext z
  constructor
  · intro hz; exact C.toGlueInput.ιX0.isOpenEmbedding.injective hz
  · rintro rfl; rfl

p2m_export "V3Glue.ChartInput" "comap_ιX0_compG_inl"

theorem compG_prod_comap_ιX0_eq [Fintype N] (hx : ∀ n, IsClosed ({C.x n} : Set X))
    (J : (C.X0 : Scheme.{0}).IdealSheafData) (hrad : J.radical = J)
    (hdisj : Disjoint (⟨closure ({(⟨ξ 0, hξ 0⟩ : C.X0)} : Set C.X0), isClosed_closure⟩ : Closeds C.X0)
      ⟨closure ({(⟨ξ 1, hξ 1⟩ : C.X0)} : Set C.X0), isClosed_closure⟩)
    (hsupp : J.support = (⟨closure ({(⟨ξ 0, hξ 0⟩ : C.X0)} : Set C.X0), isClosed_closure⟩ : Closeds C.X0) ⊔
      ⟨closure ({(⟨ξ 1, hξ 1⟩ : C.X0)} : Set C.X0), isClosed_closure⟩) :
    (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 = J := by
  classical
  rw [comap_finset_prod, Fintype.prod_sum_type]
  have hinr : ∏ b : (Σ n : N, Fin (C.thick n - 1)), (C.compG hRF gRes hgRes ξ hξ (Sum.inr b)).comap C.toGlueInput.ιX0 = 1 :=
    Finset.prod_eq_one fun b _ => by
      obtain ⟨n, k⟩ := b
      rw [C.comap_ιX0_compG_inr hRF gRes hgRes ξ hξ hx n k]; rfl
  rw [hinr, mul_one]
  simp_rw [C.comap_ιX0_compG_inl hRF gRes hgRes ξ hξ]
  let Z : Fin 2 → Closeds C.X0 := fun j => ⟨closure ({(⟨ξ j, hξ j⟩ : C.X0)} : Set C.X0), isClosed_closure⟩
  change ∏ j, vanishingIdeal (Z j) = J
  apply prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup Z
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hdisj
    · exact hdisj.symm
    · exact absurd rfl hij
  · exact hrad
  · rw [hsupp]
    apply le_antisymm
    · exact sup_le (le_iSup Z 0) (le_iSup Z 1)
    · refine iSup_le fun j => ?_
      fin_cases j
      · exact le_sup_left
      · exact le_sup_right

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

section glue

variable [Fintype N] {T : Scheme.{0}} (b : C.toGlueInput.glued ⟶ T)

private theorem _root_.V3Glue.ChartInput.compG_prod_eq_comap (K : T.IdealSheafData)
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 = K.comap (C.toGlueInput.ιX0 ≫ b))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) = K.comap (C.toGlueInput.ιY n ≫ b)) :
    ∏ v, C.compG hRF gRes hgRes ξ hξ v = K.comap b := by
  apply eq_of_forall_comap_openCover_eq C.toGlueInput.openCover
  rintro (_ | n)
  · exact hX0.trans (comap_comp K C.toGlueInput.ιX0 b)
  · exact (hY n).trans (comap_comp K (C.toGlueInput.ιY n) b)

p2m_export "V3Glue.ChartInput" "compG_prod_eq_comap"

private theorem _root_.V3Glue.ChartInput.compG_prod_eq_ofIdealTop_span (r : Γ(T, ⊤))
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 =
      (ofIdealTop (Ideal.span {r})).comap (C.toGlueInput.ιX0 ≫ b))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) =
      (ofIdealTop (Ideal.span {r})).comap (C.toGlueInput.ιY n ≫ b)) :
    ∏ v, C.compG hRF gRes hgRes ξ hξ v = ofIdealTop (Ideal.span {b.appTop.hom r}) := by
  rw [C.compG_prod_eq_comap hRF gRes hgRes ξ hξ b _ hX0 hY, comap_ofIdealTop, Ideal.map_span, Set.image_singleton]

p2m_export "V3Glue.ChartInput" "compG_prod_eq_ofIdealTop_span"

theorem compG_prod_ideal_eq_span_natCast' (p : ℕ)
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 =
      (ofIdealTop (Ideal.span {((p : ℕ) : Γ(T, ⊤))})).comap (C.toGlueInput.ιX0 ≫ b))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) =
      (ofIdealTop (Ideal.span {((p : ℕ) : Γ(T, ⊤))})).comap (C.toGlueInput.ιY n ≫ b))
    (U : C.toGlueInput.glued.affineOpens) :
    (∏ v, C.compG hRF gRes hgRes ξ hξ v).ideal U = Ideal.span {((p : ℕ) : Γ(C.toGlueInput.glued, U))} := by
  rw [C.compG_prod_eq_ofIdealTop_span hRF gRes hgRes ξ hξ b _ hX0 hY, ofIdealTop_ideal, Ideal.map_span,
    Set.image_singleton, map_natCast, map_natCast]

end glue
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private def _root_.V3Glue.ChartInput.toBase : C.toGlueInput.glued ⟶ C.B := C.toGlueInput.toDR ≫ C.πX

p2m_export "V3Glue.ChartInput" "toBase"
@[reassoc]
private theorem _root_.V3Glue.ChartInput.ιX0_toBase : C.toGlueInput.ιX0 ≫ C.toBase = (C.X0 : X.Opens).ι ≫ C.πX := by
  rw [toBase, ← Category.assoc, C.toGlueInput.ιX0_toDR]; rfl

p2m_export "V3Glue.ChartInput" "ιX0_toBase ιX0_toBase_assoc"
@[reassoc]
private theorem _root_.V3Glue.ChartInput.ιY_toBase (n : N) : C.toGlueInput.ιY n ≫ C.toBase = C.toB n := by
  rw [toBase, ← Category.assoc, C.toGlueInput.ιY_toDR, toB_eq, Category.assoc]; rfl

p2m_export "V3Glue.ChartInput" "ιY_toBase ιY_toBase_assoc"
section glueBase

variable [Fintype N]
  (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

private theorem _root_.V3Glue.ChartInput.compG_prod_eq_comap_toBase (P : C.B.IdealSheafData)
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 = P.comap ((C.X0 : X.Opens).ι ≫ C.πX))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) = P.comap (C.toB n)) :
    ∏ v, C.compG hRF gRes hgRes ξ hξ v = P.comap C.toBase :=
  C.compG_prod_eq_comap hRF gRes hgRes ξ hξ C.toBase P (by rw [hX0, ιX0_toBase]; rfl)
    (fun n => by rw [hY, ιY_toBase]; rfl)

p2m_export "V3Glue.ChartInput" "compG_prod_eq_comap_toBase"

theorem compG_prod_ideal_eq_span_natCast (p : ℕ)
    (hX0 : (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap C.toGlueInput.ιX0 =
      (ofIdealTop (Ideal.span {((p : ℕ) : Γ(C.B, ⊤))})).comap ((C.X0 : X.Opens).ι ≫ C.πX))
    (hY : ∀ n, (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) =
      (ofIdealTop (Ideal.span {((p : ℕ) : Γ(C.B, ⊤))})).comap (C.toB n))
    (U : C.toGlueInput.glued.affineOpens) :
    (∏ v, C.compG hRF gRes hgRes ξ hξ v).ideal U = Ideal.span {((p : ℕ) : Γ(C.toGlueInput.glued, U))} := by
  rw [C.compG_prod_eq_comap_toBase hRF gRes hgRes ξ hξ _ hX0 hY, comap_ofIdealTop, Ideal.map_span, Set.image_singleton,
    ofIdealTop_ideal, Ideal.map_span, Set.image_singleton, map_natCast, map_natCast]

end glueBase
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian LocallyOfFiniteType.stalkMap IsProper basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsZariskiLocalAtSource.of_openCover stalkwise FormallyUnramified.stalkMap Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth Scheme.IdealSheafData.vanishingIdeal isReduced_of_isIntegral isReduced_of_isReduced_stalk IsZariskiLocalAtSource IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isLocallyNoetherian_iff_openCover Flat.stalkMap Flat IsReduced HasRingHomProperty.Spec_iff isAffineOpen_top Scheme.preimage_basicOpen_top Etale IsAffineOpen IsNoetherian FormallyUnramified Flat.generalizingMap isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Hom.comp_apply basicOpen_eq_of_affine Scheme.IdealSheafData Scheme.ΓSpecIso v3_isReduced_pullback_subschemeι_of_isOpenImmersion Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing Smooth.isReduced_of_isReduced_of_isLocallyNoetherian Scheme.isIntegral_subscheme_vanishingIdeal Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing"
p2m_open "AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq"

open V3Glue.Aux

theorem isReduced_pullback_comp_iso_hom {X Y F F' : Scheme.{u}} (f : X ⟶ Y) (i' : F' ⟶ Y) (e : F ≅ F')
    [IsReduced (Limits.pullback f i')] : IsReduced (Limits.pullback f (e.hom ≫ i')) :=
  isReduced_of_isOpenImmersion
    ((Limits.pullbackLeftPullbackSndIso f i' e.hom).inv ≫ Limits.pullback.fst (Limits.pullback.snd f i') e.hom)

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry V3Glue.Aux.Layer0 TopologicalSpace AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section strictPoints

variable (n : N)

private theorem _root_.V3Glue.ChartInput.isReduced_pullback_g_iff {F : Scheme.{0}} (i : F ⟶ C.Res n) :
    IsReduced (pullback (C.g n) i) ↔ IsReduced (pullback (C.f n) (i ≫ C.ρ n)) := by
  let A : pullback (C.g n) i ≅ pullback (C.f n) (i ≫ C.ρ n) := pullbackLeftPullbackSndIso (C.f n) (C.ρ n) i
  exact ⟨fun _ => isReduced_of_isOpenImmersion A.inv, fun _ => isReduced_of_isOpenImmersion A.hom⟩

p2m_export "V3Glue.ChartInput" "isReduced_pullback_g_iff"

private theorem _root_.V3Glue.ChartInput.eq_j_of_q_mem_X0 (y : C.Y n) (hy : ((C.q n).base y).1 ∈ C.X0) :
    y = C.j n ⟨((C.q n).base y).1, ((C.q n).base y).2, hy⟩ := by
  obtain ⟨w, hw⟩ := C.hq n y hy
  have hqw : (C.q n).base (C.j n w) = ⟨w.1, w.2.1⟩ := by
    have h := congrArg (fun φ => φ.base w) (C.j_q n)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [h]
    exact Subtype.ext (by
      have h2 := congrArg (fun φ => φ.base w) (X.homOfLE_ι (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n))
      simpa using h2)
  subst hw
  congr 1
  exact Subtype.ext (congrArg Subtype.val hqw).symm

p2m_export "V3Glue.ChartInput" "eq_j_of_q_mem_X0"

theorem preimage_g_singleton_eq (lam : C.Res n) (u : ↥(C.U n)) (hu : (u : X) ∈ C.X0)
    (hf : (C.f n).base ⁻¹' {C.ρ n lam} = {u}) (hρ : (C.ρ n).base ⁻¹' {C.ρ n lam} = {lam}) :
    (C.g n).base ⁻¹' {lam} = {C.j n ⟨u, u.2, hu⟩} := by
  have hfq : ∀ y : C.Y n, C.f n (C.q n y) = C.ρ n (C.g n y) := fun y => by
    rw [← Scheme.Hom.comp_apply, C.q_f, Scheme.Hom.comp_apply]
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hy
    have hqu : C.q n y = u := by
      have : C.q n y ∈ (C.f n).base ⁻¹' {C.ρ n lam} := by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        change C.f n (C.q n y) = _
        rw [hfq, show C.g n y = lam from hy]
      rw [hf] at this
      exact this
    have hy0 : ((C.q n).base y).1 ∈ C.X0 := by
      rw [show (C.q n).base y = u from hqu]; exact hu
    rw [C.eq_j_of_q_mem_X0 n y hy0]
    congr 2
    exact congrArg Subtype.val hqu
  · rintro rfl
    have h1 : C.g n (C.j n ⟨u, u.2, hu⟩) ∈ (C.ρ n).base ⁻¹' {C.ρ n lam} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      change C.ρ n (C.g n _) = _
      rw [← hfq]
      have hq : C.q n (C.j n ⟨u, u.2, hu⟩) = u := by
        rw [← Scheme.Hom.comp_apply, C.j_q]
        exact Subtype.ext (by
          have h2 := congrArg (fun φ => φ.base ⟨u, u.2, hu⟩) (X.homOfLE_ι (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n))
          simpa using h2)
      rw [hq]
      have hu' : u ∈ (C.f n).base ⁻¹' {C.ρ n lam} := by rw [hf]; rfl
      exact hu'
    rw [hρ] at h1
    exact h1

end strictPoints
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

section strictBridge

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

private theorem _root_.V3Glue.ChartInput.preimage_ιY_support_compG_inl (n : N) (j : Fin 2) (hU : ξ j ∈ C.U n) :
    (C.toGlueInput.ιY n).base ⁻¹' ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).support : Set C.toGlueInput.glued) =
      closure ({C.ξY ξ hξ n j hU} : Set (C.Y n)) := by
  rw [coe_support_compG, ← C.ιY_ξY hRF gRes hgRes ξ hξ n j hU,
    (C.toGlueInput.ιY n).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage (C.toGlueInput.ιY n).continuous]
  congr 1
  ext z
  constructor
  · intro hz
    exact (C.toGlueInput.ιY n).isOpenEmbedding.injective hz
  · rintro rfl
    exact rfl

p2m_export "V3Glue.ChartInput" "preimage_ιY_support_compG_inl"

private theorem _root_.V3Glue.ChartInput.comap_ιY_compG_inl (n : N) (j : Fin 2) (hU : ξ j ∈ C.U n) (L : (C.Res n).IdealSheafData) (lam : C.Res n)
    [IsReduced (pullback (C.g n) L.subschemeι)]
    (hLsupp : (L.support : Set (C.Res n)) = closure {lam})
    (hlam : (C.g n).base ⁻¹' {lam} = {C.ξY ξ hξ n j hU}) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).comap (C.toGlueInput.ιY n) = L.comap (C.g n) := by
  rw [compG, comap_vanishingIdeal_of_isOpenImmersion, v3_comap_eq_vanishingIdeal_of_isReduced]
  congr 1
  ext1
  change (C.toGlueInput.ιY n).base ⁻¹' closure {C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)} = (C.g n).base ⁻¹' (L.support : Set _)
  have h1 := C.preimage_ιY_support_compG_inl hRF gRes hgRes ξ hξ n j hU
  rw [coe_support_compG] at h1
  rw [h1, hLsupp, (C.g n).isOpenMap.preimage_closure_eq_closure_preimage (C.g n).continuous, hlam]

p2m_export "V3Glue.ChartInput" "comap_ιY_compG_inl"

theorem comap_ιY_compG_inr' (n : N) (k : Fin (C.thick n - 1))
    (hfib : IsIso ((C.f n).fiberToSpecResidueField (C.vertex n)))
    (L : (C.Res n).IdealSheafData) [IsReduced L.subscheme]
    (t : L.subscheme ⟶ Spec ((C.S n).residueField (C.vertex n)))
    (ht : L.subschemeι ≫ C.ρ n = t ≫ (C.S n).fromSpecResidueField (C.vertex n))
    (hLsupp : (L.support : Set (C.Res n)) = closure {gRes n k}) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).comap (C.toGlueInput.ιY n) = L.comap (C.g n) :=
  C.comap_ιY_compG_inr hRF gRes hgRes ξ hξ n k hfib L t ht hLsupp (by unfold compG; infer_instance)

end strictBridge
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

section etaleReduced

namespace Algebra p2m_export "Algebra" "EssFiniteType FormallyUnramified.map_maximalIdeal trace TensorProduct.includeRight mk algebraMap TensorProduct.lid FormallyUnramified comap_top smoothLocus Smooth Etale smul_def TensorProduct.includeRight_apply mem_bot coe_bot FormallyUnramified.isReduced_of_field" namespace FormallyUnramified p2m_export "Algebra.FormallyUnramified" "map_maximalIdeal ext comp mk isReduced_of_field" end Algebra.FormallyUnramified
p2m_open_scoped "Algebra Algebra.FormallyUnramified" in
open TensorProduct in

theorem Algebra.FormallyUnramified.isReduced_of_isDomain_of_flat (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [Algebra A B] [Module.Flat A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] : IsReduced B := by
  let K := FractionRing A
  haveI : IsReduced (K ⊗[A] B) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[A] B)
  let φ : B →ₐ[A] K ⊗[A] B := Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ := by
    have h1 : Function.Injective ((Algebra.linearMap A K).rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective A K)
    have hφ' : ⇑φ = ((Algebra.linearMap A K).rTensor B) ∘ (TensorProduct.lid A B).symm := by
      ext b
      simp [φ, Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul]
    rw [hφ']
    exact h1.comp (TensorProduct.lid A B).symm.injective
  exact isReduced_of_injective φ hφ

end etaleReduced
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian LocallyOfFiniteType.stalkMap IsProper basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsZariskiLocalAtSource.of_openCover stalkwise FormallyUnramified.stalkMap Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth Scheme.IdealSheafData.vanishingIdeal isReduced_of_isIntegral isReduced_of_isReduced_stalk IsZariskiLocalAtSource IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isLocallyNoetherian_iff_openCover Flat.stalkMap Flat IsReduced HasRingHomProperty.Spec_iff isAffineOpen_top Scheme.preimage_basicOpen_top Etale IsAffineOpen IsNoetherian FormallyUnramified Flat.generalizingMap isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Hom.comp_apply basicOpen_eq_of_affine Scheme.IdealSheafData Scheme.ΓSpecIso v3_isReduced_pullback_subschemeι_of_isOpenImmersion Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing Smooth.isReduced_of_isReduced_of_isLocallyNoetherian Scheme.isIntegral_subscheme_vanishingIdeal Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing"
p2m_open "AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq"

open V3Glue.Aux

theorem isReduced_of_flat_of_formallyUnramified_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [FormallyUnramified f] [LocallyOfFiniteType f] [IsIntegral Y] : IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    haveI : Algebra.FormallyUnramified (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      FormallyUnramified.stalkMap f x
    haveI : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      LocallyOfFiniteType.stalkMap f x
    exact Algebra.FormallyUnramified.isReduced_of_isDomain_of_flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
  exact isReduced_of_isReduced_stalk X

namespace Etale p2m_export "AlgebraicGeometry.Etale" "mk" end Etale
p2m_open_scoped "AlgebraicGeometry.Etale" in
theorem Etale.isReduced_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsIntegral Y] : IsReduced X :=
  haveI : Flat f := inferInstance
  isReduced_of_flat_of_formallyUnramified_of_isIntegral f

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private theorem _root_.V3Glue.ChartInput.isReduced_pullback_g_of_etale (n : N) [Etale (C.f n)] {F : Scheme.{0}} (i : F ⟶ C.Res n) [IsIntegral F] :
    IsReduced (pullback (C.g n) i) := by
  rw [C.isReduced_pullback_g_iff n i]
  exact Etale.isReduced_of_isIntegral (pullback.snd (C.f n) (i ≫ C.ρ n))

p2m_export "V3Glue.ChartInput" "isReduced_pullback_g_of_etale"

theorem comap_ιY_compG_inl_of_etale
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
    (n : N) [Etale (C.f n)] (j : Fin 2) (hU : ξ j ∈ C.U n) (L : (C.Res n).IdealSheafData) [IsIntegral L.subscheme]
    (lam : C.Res n) (hLsupp : (L.support : Set (C.Res n)) = closure {lam})
    (hlam : (C.g n).base ⁻¹' {lam} = {C.ξY ξ hξ n j hU}) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).comap (C.toGlueInput.ιY n) = L.comap (C.g n) :=
  haveI := C.isReduced_pullback_g_of_etale n L.subschemeι
  C.comap_ιY_compG_inl hRF gRes hgRes ξ hξ n j hU L lam hLsupp hlam

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

open V3Glue.Aux

p2m_open "AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private theorem _root_.V3Glue.ChartInput.isReduced_pullback_g_of_etale' (n : N) [Etale (C.f n)] {F : Scheme.{0}} (i : F ⟶ C.Res n)
    [IsReduced F] [IsLocallyNoetherian F] : IsReduced (pullback (C.g n) i) := by
  rw [C.isReduced_pullback_g_iff n i]
  exact Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd (C.f n) (i ≫ C.ρ n))

p2m_export "V3Glue.ChartInput" "isReduced_pullback_g_of_etale'"

theorem comap_ιY_compG_inl_of_etale'
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
    (n : N) [Etale (C.f n)] (j : Fin 2) (hU : ξ j ∈ C.U n) (L : (C.Res n).IdealSheafData)
    [IsReduced L.subscheme] [IsLocallyNoetherian L.subscheme]
    (lam : C.Res n) (hLsupp : (L.support : Set (C.Res n)) = closure {lam})
    (hlam : (C.g n).base ⁻¹' {lam} = {C.ξY ξ hξ n j hU}) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).comap (C.toGlueInput.ιY n) = L.comap (C.g n) :=
  haveI := C.isReduced_pullback_g_of_etale' n L.subschemeι
  C.comap_ιY_compG_inl hRF gRes hgRes ξ hξ n j hU L lam hLsupp hlam

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

end
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

p2m_open "CategoryTheory AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry IsLocalRing MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial"

noncomputable section

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsLocallyNoetherian LocallyOfFiniteType.stalkMap IsProper basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsZariskiLocalAtSource.of_openCover stalkwise FormallyUnramified.stalkMap Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth Scheme.IdealSheafData.vanishingIdeal isReduced_of_isIntegral isReduced_of_isReduced_stalk IsZariskiLocalAtSource IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isLocallyNoetherian_iff_openCover Flat.stalkMap Flat IsReduced HasRingHomProperty.Spec_iff isAffineOpen_top Scheme.preimage_basicOpen_top Etale IsAffineOpen IsNoetherian FormallyUnramified Flat.generalizingMap isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Hom.comp_apply basicOpen_eq_of_affine Scheme.IdealSheafData Scheme.ΓSpecIso v3_isReduced_pullback_subschemeι_of_isOpenImmersion Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing Smooth.isReduced_of_isReduced_of_isLocallyNoetherian Scheme.isIntegral_subscheme_vanishingIdeal Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing" namespace IsOpenImmersion p2m_export "AlgebraicGeometry.IsOpenImmersion" "comp" end AlgebraicGeometry.IsOpenImmersion
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.IsOpenImmersion" in

theorem AlgebraicGeometry.IsOpenImmersion.isRegularLocalRing_stalk_iff
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔ IsRegularLocalRing (U.presheaf.stalk u) := by
  let e : X.presheaf.stalk (i.base u) ≃+* U.presheaf.stalk u := (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e, fun h => IsRegularLocalRing.of_ringEquiv e.symm⟩

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.IsOpenImmersion" in

theorem AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    ringKrullDim (U.presheaf.stalk u) = ringKrullDim (X.presheaf.stalk (i.base u)) :=
  (ringKrullDim_eq_of_ringEquiv (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv).symm

namespace IsRegularLocalRing p2m_export "IsRegularLocalRing" "spanFinrank_maximalIdeal of_ringEquiv mk isDomain" end IsRegularLocalRing
p2m_open_scoped "IsRegularLocalRing" in

theorem IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsRegularLocalRing A] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B) :
    IsRegularLocalRing B ∧ ringKrullDim B ≤ ringKrullDim A := by
  have hreg : IsRegularLocalRing B := by
    refine RegularFlatLocalAscent.isRegularLocalRing_of_flat_of_isRegularLocalRing_quotient A B ?_
    rw [h]
    letI : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field (maximalIdeal B)
    infer_instance
  refine ⟨hreg, ?_⟩
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B), ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A), ← h]
  exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap A B) (IsNoetherian.noetherian _)

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsLocallyNoetherian LocallyOfFiniteType.stalkMap IsProper basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsZariskiLocalAtSource.of_openCover stalkwise FormallyUnramified.stalkMap Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth Scheme.IdealSheafData.vanishingIdeal isReduced_of_isIntegral isReduced_of_isReduced_stalk IsZariskiLocalAtSource IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isLocallyNoetherian_iff_openCover Flat.stalkMap Flat IsReduced HasRingHomProperty.Spec_iff isAffineOpen_top Scheme.preimage_basicOpen_top Etale IsAffineOpen IsNoetherian FormallyUnramified Flat.generalizingMap isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Hom.comp_apply basicOpen_eq_of_affine Scheme.IdealSheafData Scheme.ΓSpecIso v3_isReduced_pullback_subschemeι_of_isOpenImmersion Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing Smooth.isReduced_of_isReduced_of_isLocallyNoetherian Scheme.isIntegral_subscheme_vanishingIdeal Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.isRegularLocalRing_stalk_of_flat_of_map_maximalIdeal_eq
    {X Y : Scheme.{u}} (g : Y ⟶ X) (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (hflat : (g.stalkMap y).hom.Flat)
    (hmax : Ideal.map (g.stalkMap y).hom (maximalIdeal (X.presheaf.stalk (g.base y))) = maximalIdeal (Y.presheaf.stalk y))
    (hreg : IsRegularLocalRing (X.presheaf.stalk (g.base y))) :
    IsRegularLocalRing (Y.presheaf.stalk y) ∧
      ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (X.presheaf.stalk (g.base y)) := by
  letI := (g.stalkMap y).hom.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) := hflat
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap y).hom)
  haveI := hreg
  exact IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq _ _ hmax

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsLocallyNoetherian LocallyOfFiniteType.stalkMap IsProper basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsZariskiLocalAtSource.of_openCover stalkwise FormallyUnramified.stalkMap Scheme.preimage_basicOpen LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth Scheme.IdealSheafData.vanishingIdeal isReduced_of_isIntegral isReduced_of_isReduced_stalk IsZariskiLocalAtSource IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isLocallyNoetherian_iff_openCover Flat.stalkMap Flat IsReduced HasRingHomProperty.Spec_iff isAffineOpen_top Scheme.preimage_basicOpen_top Etale IsAffineOpen IsNoetherian FormallyUnramified Flat.generalizingMap isReduced_of_isOpenImmersion HasRingHomProperty Scheme.Hom.comp_apply basicOpen_eq_of_affine Scheme.IdealSheafData Scheme.ΓSpecIso v3_isReduced_pullback_subschemeι_of_isOpenImmersion Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing Smooth.isReduced_of_isReduced_of_isLocallyNoetherian Scheme.isIntegral_subscheme_vanishingIdeal Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing" namespace Etale p2m_export "AlgebraicGeometry.Etale" "mk" end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Etale" in

private theorem _root_.AlgebraicGeometry.Etale.isRegularLocalRing_stalk
    {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (hreg : IsRegularLocalRing (X.presheaf.stalk (g.base y))) :
    IsRegularLocalRing (Y.presheaf.stalk y) ∧
      ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (X.presheaf.stalk (g.base y)) := by
  haveI : Flat g := inferInstance
  haveI : FormallyUnramified g := inferInstance
  refine isRegularLocalRing_stalk_of_flat_of_map_maximalIdeal_eq g y (Flat.stalkMap g y) ?_ hreg
  letI := (g.stalkMap y).hom.toAlgebra
  haveI : Algebra.FormallyUnramified (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) :=
    FormallyUnramified.stalkMap g y
  haveI : Algebra.EssFiniteType (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) :=
    LocallyOfFiniteType.stalkMap g y
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap y).hom)
  exact Algebra.FormallyUnramified.map_maximalIdeal

end AlgebraicGeometry.Etale
p2m_export "" "AlgebraicGeometry.Etale.isRegularLocalRing_stalk"

namespace W5bLocal

private theorem _root_.W5bLocal.of_flat_of_map_maximalIdeal_eq
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsRegularLocalRing A] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B) :
    IsRegularLocalRing B ∧ ringKrullDim B ≤ ringKrullDim A := by
  have hreg : IsRegularLocalRing B := by
    refine RegularFlatLocalAscent.isRegularLocalRing_of_flat_of_isRegularLocalRing_quotient A B ?_
    rw [h]
    letI : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field (maximalIdeal B)
    infer_instance
  refine ⟨hreg, ?_⟩
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B), ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A), ← h]
  exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap A B) (IsNoetherian.noetherian _)

p2m_export "W5bLocal" "of_flat_of_map_maximalIdeal_eq"

private theorem _root_.W5bLocal.isRegularLocalRing_stalk_of_flat_of_map_maximalIdeal_eq
    {X Y : Scheme.{u}} (g : Y ⟶ X) (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (hflat : (g.stalkMap y).hom.Flat)
    (hmax : Ideal.map (g.stalkMap y).hom (maximalIdeal (X.presheaf.stalk (g.base y))) = maximalIdeal (Y.presheaf.stalk y))
    (hreg : IsRegularLocalRing (X.presheaf.stalk (g.base y))) :
    IsRegularLocalRing (Y.presheaf.stalk y) ∧
      ringKrullDim (Y.presheaf.stalk y) ≤ ringKrullDim (X.presheaf.stalk (g.base y)) := by
  letI := (g.stalkMap y).hom.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) := hflat
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap y).hom)
  haveI := hreg
  exact of_flat_of_map_maximalIdeal_eq _ _ hmax

p2m_export "W5bLocal" "isRegularLocalRing_stalk_of_flat_of_map_maximalIdeal_eq"

theorem isRegularLocalRing_stalk_iff_of_isOpenImmersion
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔ IsRegularLocalRing (U.presheaf.stalk u) := by
  let e : X.presheaf.stalk (i.base u) ≃+* U.presheaf.stalk u := (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e, fun h => IsRegularLocalRing.of_ringEquiv e.symm⟩

theorem isRegularLocalRing_stalk_crossingQuotient
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (z : ↥(Spec (CommRingCat.of (CrossingQuotient O ϖ)))) :
    IsRegularLocalRing ((Spec (CommRingCat.of (CrossingQuotient O ϖ))).presheaf.stalk z) := by
  haveI : IsRegularRing (CrossingQuotient O ϖ) := CrossingQuotient.isRegularRing_of_irreducible hϖ
  have hΓ : IsRegularRing Γ(Spec (CommRingCat.of (CrossingQuotient O ϖ)), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).commRingCatIsoToRingEquiv.symm
  exact IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing (isAffineOpen_top _) hΓ z trivial

end W5bLocal
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData"

p2m_open_scoped "AlgebraicGeometry" in
open W5bLocal in

theorem AlgebraicGeometry.isRegularLocalRing_stalk_and_ringKrullDim_le_two_of_smooth_or_pointwiseChart
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of O)) [IsLocallyNoetherian X]
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (y : X)
    (h : (∃ V : X.Opens, y ∈ V ∧ Smooth (V.ι ≫ πX)) ∨
      (∃ (U : X.Opens) (hyU : y ∈ U) (f : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of (CrossingQuotient O ϖ))),
        (f.stalkMap ⟨y, hyU⟩).hom.Flat ∧
        Ideal.map (f.stalkMap ⟨y, hyU⟩).hom
            (maximalIdeal ((Spec (CommRingCat.of (CrossingQuotient O ϖ))).presheaf.stalk (f.base ⟨y, hyU⟩))) =
          maximalIdeal ((U : Scheme.{u}).presheaf.stalk ⟨y, hyU⟩))) :
    IsRegularLocalRing (X.presheaf.stalk y) ∧ ringKrullDim (X.presheaf.stalk y) ≤ 2 := by
  refine ⟨?_, hdim y⟩
  rcases h with ⟨V, hyV, hsm⟩ | ⟨U, hyU, f, hflat, hmax⟩
  ·
    haveI := hsm
    have hV := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing O (V.ι ≫ πX) ⟨y, hyV⟩
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion V.ι ⟨y, hyV⟩).mpr hV
  ·
    haveI : IsNoetherianRing ((U : Scheme.{u}).presheaf.stalk ⟨y, hyU⟩) := inferInstance
    have hU := (isRegularLocalRing_stalk_of_flat_of_map_maximalIdeal_eq f ⟨y, hyU⟩ hflat hmax
      (isRegularLocalRing_stalk_crossingQuotient hϖ _)).1
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion U.ι ⟨y, hyU⟩).mpr hU

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

scoped instance etale_g (n : N) [Etale (C.f n)] : Etale (C.g n) :=
  MorphismProperty.pullback_snd _ _ inferInstance

private theorem _root_.V3Glue.ChartInput.isRegularLocalRing_stalk_glued_and_ringKrullDim_le_two
    [∀ n, Etale (C.f n)] [∀ n, IsLocallyNoetherian (C.Res n)]
    (hRes : ∀ n (z : C.Res n),
      IsRegularLocalRing ((C.Res n).presheaf.stalk z) ∧ ringKrullDim ((C.Res n).presheaf.stalk z) ≤ 2)
    (P : X → Prop)
    (hX0 : ∀ x0 : C.X0, P x0.1 →
      IsRegularLocalRing (((C.X0 : X.Opens) : Scheme.{0}).presheaf.stalk x0) ∧
        ringKrullDim (((C.X0 : X.Opens) : Scheme.{0}).presheaf.stalk x0) ≤ 2)
    (y : C.toGlueInput.glued) (hy : P (C.toGlueInput.toDR.base y)) :
    IsRegularLocalRing (C.toGlueInput.glued.presheaf.stalk y) ∧
      ringKrullDim (C.toGlueInput.glued.presheaf.stalk y) ≤ 2 := by
  rcases C.toGlueInput.ι_jointly_surjective y with ⟨x0, rfl⟩ | ⟨n, yn, rfl⟩
  ·
    have hP : P x0.1 := by
      have h := congr($(C.toGlueInput.ιX0_toDR).base x0)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      rw [h] at hy
      simpa using hy
    obtain ⟨h1, h2⟩ := hX0 x0 hP
    exact ⟨(IsOpenImmersion.isRegularLocalRing_stalk_iff C.toGlueInput.ιX0 x0).mpr h1,
      (IsOpenImmersion.ringKrullDim_stalk_eq C.toGlueInput.ιX0 x0) ▸ h2⟩
  ·
    haveI : IsLocallyNoetherian (C.Y n) := LocallyOfFiniteType.isLocallyNoetherian (C.g n)
    obtain ⟨h1, h2⟩ := AlgebraicGeometry.Etale.isRegularLocalRing_stalk (C.g n) yn (hRes n _).1
    refine ⟨(IsOpenImmersion.isRegularLocalRing_stalk_iff (C.toGlueInput.ιY n) yn).mpr h1, ?_⟩
    rw [← IsOpenImmersion.ringKrullDim_stalk_eq (C.toGlueInput.ιY n) yn]
    exact h2.trans (hRes n _).2

p2m_export "V3Glue.ChartInput" "isRegularLocalRing_stalk_glued_and_ringKrullDim_le_two"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue"

namespace MvPolynomial
p2m_export "MvPolynomial" "comap_comp X map constantCoeff R ringKrullDim_of_isNoetherianRing ext support comap coe_add vanishingIdeal C rTensor monomial coe_one induction_on CrossingQuotient.Resolution CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient CrossingQuotient.isRegularRing_of_irreducible CrossingQuotient.Resolution.isRegularLocalRing_stalk CrossingQuotient.lineUIdeal CrossingQuotient.algebraMap_mem_span_U CrossingQuotient.lineUIdeal_eq_span_sup_map CrossingQuotient.Resolution.lineUGen CrossingQuotient.Resolution.origin_injective CrossingQuotient.Resolution.lineUGen_injective CrossingQuotient.Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme chartScheme Resolution Resolution.ι Resolution.exists_ι_apply_eq Resolution.toSpec U V U_mul_V resolutionChart resolutionChart_U resolutionChart_V mk monomial linearIndependent_monomial_and_span_eq_top isRegularRing_of_irreducible Resolution.isRegularLocalRing_stalk lineUIdeal algebraMap_mem_span_U lineUIdeal_eq_span_sup_map Resolution.lineUGen Resolution.origin_injective Resolution.lineUGen_injective Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq openCover chartToCrossing toCrossing ι_toCrossing toSpec ι_toSpec isRegularLocalRing_stalk lineGen lineUGen origin_injective lineUGen_injective eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

attribute [scoped instance] MvPolynomial.CrossingQuotient.Resolution.isLocallyNoetherian

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput"

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private theorem _root_.V3Glue.ChartInput.hX0_of_stalk (P : X → Prop)
    (h : ∀ x : X, x ∈ C.X0 → P x → IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) ≤ 2) :
    ∀ x0 : C.X0, P x0.1 →
      IsRegularLocalRing (((C.X0 : X.Opens) : Scheme.{0}).presheaf.stalk x0) ∧
        ringKrullDim (((C.X0 : X.Opens) : Scheme.{0}).presheaf.stalk x0) ≤ 2 := by
  intro x0 hP
  obtain ⟨h1, h2⟩ := h x0.1 x0.2 hP
  have hb : (C.X0.ι).base x0 = x0.1 := rfl
  refine ⟨(IsOpenImmersion.isRegularLocalRing_stalk_iff C.X0.ι x0).mp (hb ▸ h1), ?_⟩
  rw [IsOpenImmersion.ringKrullDim_stalk_eq C.X0.ι x0]
  exact hb ▸ h2

p2m_export "V3Glue.ChartInput" "hX0_of_stalk"

private theorem _root_.V3Glue.ChartInput.isRegularLocalRing_stalk_glued_and_ringKrullDim_le_two'
    [∀ n, Etale (C.f n)] [∀ n, IsLocallyNoetherian (C.Res n)]
    (hRes : ∀ n (z : C.Res n),
      IsRegularLocalRing ((C.Res n).presheaf.stalk z) ∧ ringKrullDim ((C.Res n).presheaf.stalk z) ≤ 2)
    (P : X → Prop)
    (hX : ∀ x : X, x ∈ C.X0 → P x → IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (y : C.toGlueInput.glued) (hy : P (C.toGlueInput.toDR.base y)) :
    IsRegularLocalRing (C.toGlueInput.glued.presheaf.stalk y) ∧
      ringKrullDim (C.toGlueInput.glued.presheaf.stalk y) ≤ 2 :=
  C.isRegularLocalRing_stalk_glued_and_ringKrullDim_le_two hRes P (C.hX0_of_stalk P hX) y hy

p2m_export "V3Glue.ChartInput" "isRegularLocalRing_stalk_glued_and_ringKrullDim_le_two'"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"

end
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry IsLocalRing MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient"

namespace MvPolynomial
p2m_export "MvPolynomial" "comap_comp X map constantCoeff R ringKrullDim_of_isNoetherianRing ext support comap coe_add vanishingIdeal C rTensor monomial coe_one induction_on CrossingQuotient.Resolution CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient CrossingQuotient.isRegularRing_of_irreducible CrossingQuotient.Resolution.isRegularLocalRing_stalk CrossingQuotient.lineUIdeal CrossingQuotient.algebraMap_mem_span_U CrossingQuotient.lineUIdeal_eq_span_sup_map CrossingQuotient.Resolution.lineUGen CrossingQuotient.Resolution.origin_injective CrossingQuotient.Resolution.lineUGen_injective CrossingQuotient.Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "crossingScheme chartScheme Resolution Resolution.ι Resolution.exists_ι_apply_eq Resolution.toSpec U V U_mul_V resolutionChart resolutionChart_U resolutionChart_V mk monomial linearIndependent_monomial_and_span_eq_top isRegularRing_of_irreducible Resolution.isRegularLocalRing_stalk lineUIdeal algebraMap_mem_span_U lineUIdeal_eq_span_sup_map Resolution.lineUGen Resolution.origin_injective Resolution.lineUGen_injective Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen"
p2m_open "MvPolynomial.CrossingQuotient MvPolynomial"

theorem ringKrullDim_stalk_crossingScheme_le {W : Type u} [CommRing W] (s : W) (y : crossingScheme s) :
    ringKrullDim ((crossingScheme s).presheaf.stalk y) ≤ ringKrullDim (CrossingQuotient W s) := by
  letI : Algebra Γ(crossingScheme s, ⊤) ((crossingScheme s).presheaf.stalk y) :=
    ((crossingScheme s).presheaf.germ ⊤ y trivial).hom.toAlgebra
  haveI := (isAffineOpen_top (crossingScheme s)).isLocalization_stalk ⟨y, trivial⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height ((isAffineOpen_top (crossingScheme s)).primeIdealOf ⟨y, trivial⟩).asIdeal
    ((crossingScheme s).presheaf.stalk y), ← ringKrullDim_eq_of_ringEquiv
      (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W s))).commRingCatIsoToRingEquiv]
  exact Ideal.height_le_ringKrullDim_of_isPrime

namespace Resolution p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq openCover chartToCrossing toCrossing ι_toCrossing toSpec ι_toSpec isRegularLocalRing_stalk lineGen lineUGen origin_injective lineUGen_injective eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen" end Resolution
p2m_open_scoped "MvPolynomial.CrossingQuotient.Resolution" in

theorem Resolution.ringKrullDim_stalk_le_two {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) (z : Resolution ϖ e) :
    ringKrullDim ((Resolution ϖ e).presheaf.stalk z) ≤ 2 := by
  obtain ⟨i, y, rfl⟩ := Resolution.exists_ι_apply_eq ϖ e z
  rw [← ringKrullDim_eq_of_ringEquiv (asIso ((Resolution.ι ϖ e i).stalkMap y)).commRingCatIsoToRingEquiv.symm]
  refine (ringKrullDim_stalk_crossingScheme_le ϖ y).trans ?_

  have hf : (X 0 * X 1 - C ϖ : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have h0 := congrArg MvPolynomial.constantCoeff h
    simp at h0
    exact hϖ.ne_zero h0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one R (IsDiscreteValuationRing.not_isField R),
    Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  change ringKrullDim (CrossingQuotient R ϖ) + 1 ≤ _ at h1
  generalize ringKrullDim (CrossingQuotient R ϖ) = q at h1 ⊢
  induction q using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe q =>
    induction q using ENat.recTopCoe with
    | top =>
      exfalso
      have e1 : (((⊤ : ℕ∞) : WithBot ℕ∞) + 1) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e1] at h1
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((3 : ℕ∞) : WithBot ℕ∞) := h1.trans (le_of_eq (by norm_num))
      exact absurd (WithBot.coe_le_coe.mp h2) (not_le_of_gt (ENat.coe_lt_top 3))
    | coe d =>
      rw [← WithBot.coe_one, ← WithBot.coe_add] at h1
      have h2 : ((d : ℕ∞) + 1 : ℕ∞) ≤ (3 : ℕ∞) := by
        have h3 : (((d : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((3 : ℕ∞) : WithBot ℕ∞) := h1.trans (le_of_eq (by norm_num))
        exact WithBot.coe_le_coe.mp h3
      have h3 : d + 1 ≤ 3 := by exact_mod_cast h2
      have h4 : ((d : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (by exact_mod_cast (show d ≤ 2 by omega))
      exact h4.trans (le_of_eq (by norm_num))

end MvPolynomial.CrossingQuotient
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry ModularCurve"

section S29Tails
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~IsOpenImmersion.isRegularLocalRing_stalk_iff~IsOpenImmersion.ringKrullDim_stalk_eq P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry TopologicalSpace"
namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

private theorem _root_.V3Glue.ChartInput.x_not_mem_X0 (n : N) : C.x n ∉ C.X0 := fun h => (C.mem_X0 (C.x n)).mp h n rfl

p2m_export "V3Glue.ChartInput" "x_not_mem_X0"

private theorem _root_.V3Glue.ChartInput.ηG_injective (hξ01 : ξ 0 ≠ ξ 1) (hgRes_inj : ∀ n, Function.Injective (gRes n)) :
    Function.Injective (C.ηG hRF gRes hgRes ξ hξ) := by
  rintro (j | ⟨n, k⟩) (j' | ⟨m, k'⟩) h
  ·
    have h' : ξ j = ξ j' := by
      have := congrArg (fun y => C.toGlueInput.toDR y) h
      simpa only [toDR_ηG_inl] using this
    rcases fin_two_eq_zero_or_one j with rfl | rfl <;> rcases fin_two_eq_zero_or_one j' with rfl | rfl
    · rfl
    · exact absurd h' hξ01
    · exact absurd h'.symm hξ01
    · rfl
  ·
    exfalso
    have := congrArg (fun y => C.toGlueInput.toDR y) h
    simp only [toDR_ηG_inl, toDR_ηG_inr] at this
    exact C.x_not_mem_X0 m (this ▸ hξ j)
  · exfalso
    have := congrArg (fun y => C.toGlueInput.toDR y) h
    simp only [toDR_ηG_inl, toDR_ηG_inr] at this
    exact C.x_not_mem_X0 n (this.symm ▸ hξ j')
  ·
    by_cases hnm : n = m
    · subst hnm
      have hk : k = k' := C.exPt_injective n (hRF n) (gRes n) (hgRes n) (hgRes_inj n) (by simpa only [ηG_inr] using h)
      subst hk
      rfl
    · exfalso
      exact C.exPt_ne_of_ne hnm (hRF n) (hRF m) _ _ _ _ (by simpa only [ηG_inr] using h)

p2m_export "V3Glue.ChartInput" "ηG_injective"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"

namespace V3Glue
p2m_export "V3Glue" "ChartInput.coe_support_compG GlueInput ChartInput RawChartInput SiteAux.locallyOfFinitePresentation_of_isLocallyNoetherian Site.XO Site.Node Site.xpt ChartInput.isReduced_Y"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "Comps ηG ηG_inl ηG_inr compG coe_support_compG toDR_ηG_inl toDR_ηG_inr exc_image' ξY ιY_ξY comap_ιY_compG_inr apply_not_mem_of_mem_support_compG fin_two_eq_zero_or_one ηG_inr_eq_of_specializes ηG_inl_eq_of_specializes xU vertex exPt toDR_exPt exPt_injective exPt_ne_of_ne toDR_edgePt' edgePt'_injective Y q a j j_q toGlueInput hq g q_f toB toB_eq flat_q_ι_πX interior_setOf_q_eq πX Res X0 interior_preimage_vertex f_etale U isLocallyNoetherian_Res mk S B ρ flat_ρ_σ x thick f mem_X0 isReduced_Y"
p2m_open "V3Glue.ChartInput V3Glue"

open TopologicalSpace V3Glue.Aux.Layer0.W6a

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

private theorem _root_.V3Glue.ChartInput.ηG_not_mem_closure {T : Scheme.{0}} (b : C.toGlueInput.glued ⟶ T) (V : T.Opens)
    (hinj : Function.Injective (C.ηG hRF gRes hgRes ξ hξ))
    (hfib : ∀ w, b.base (C.ηG hRF gRes hgRes ξ hξ w) ∉ V)
    (hmax : ∀ v (y : C.toGlueInput.glued), y ⤳ C.ηG hRF gRes hgRes ξ hξ v → b.base y ∉ V → y = C.ηG hRF gRes hgRes ξ hξ v)
    (v w : C.Comps) (hvw : v ≠ w) :
    C.ηG hRF gRes hgRes ξ hξ v ∉ closure {C.ηG hRF gRes hgRes ξ hξ w} := by
  intro hcl
  have hsp : C.ηG hRF gRes hgRes ξ hξ w ⤳ C.ηG hRF gRes hgRes ξ hξ v := specializes_iff_mem_closure.mpr hcl
  exact hvw (hinj (hmax v _ hsp (hfib w)).symm)

p2m_export "V3Glue.ChartInput" "ηG_not_mem_closure"

theorem η_stalk' {T : Scheme.{0}} (b : C.toGlueInput.glued ⟶ T) (V : T.Opens)
    (hinj : Function.Injective (C.ηG hRF gRes hgRes ξ hξ))
    (hfib : ∀ w, b.base (C.ηG hRF gRes hgRes ξ hξ w) ∉ V)
    (hmax : ∀ v (y : C.toGlueInput.glued), y ⤳ C.ηG hRF gRes hgRes ξ hξ v → b.base y ∉ V → y = C.ηG hRF gRes hgRes ξ hξ v)
    (v : C.Comps) :
    ∃ (U : C.toGlueInput.glued.affineOpens) (hU : C.ηG hRF gRes hgRes ξ hξ v ∈ (U : C.toGlueInput.glued.Opens)),
      Ideal.map (C.toGlueInput.glued.presheaf.germ (U : C.toGlueInput.glued.Opens) (C.ηG hRF gRes hgRes ξ hξ v) hU).hom
          ((C.compG hRF gRes hgRes ξ hξ v).ideal U) =
        IsLocalRing.maximalIdeal (C.toGlueInput.glued.presheaf.stalk (C.ηG hRF gRes hgRes ξ hξ v)) ∧
      ∀ w, w ≠ v → Ideal.map (C.toGlueInput.glued.presheaf.germ (U : C.toGlueInput.glued.Opens) (C.ηG hRF gRes hgRes ξ hξ v) hU).hom
          ((C.compG hRF gRes hgRes ξ hξ w).ideal U) = ⊤ :=
  exists_affineOpens_map_germ_vanishingIdeal_closure (C.ηG hRF gRes hgRes ξ hξ)
    (C.ηG_not_mem_closure hRF gRes hgRes ξ hξ b V hinj hfib hmax) v

end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"

end S29Tails
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"

namespace V3SolH

section Index
variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

def node_fintype : Fintype (V3Glue.Site.Node p 𝔛 κ) := by
  classical
  haveI : Finite (V3Glue.Site.Node p 𝔛 κ) := by
    apply Nat.finite_of_card_ne_zero
    rw [𝔛.crossing_card κ]
    haveI : Finite ↥(ssJSet p κ) := (ssJSet_finite p κ).to_subtype
    haveI : Nonempty ↥(ssJSet p κ) := (ssJSet_nonempty (q := p) (k := κ)).to_subtype
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  exact Fintype.ofFinite _

end Index
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"

attribute [local instance] node_fintype

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) (H : V3Asm.SiteHyps p 𝔛 O κ toκ)

include hϖ in

theorem p_ne_zero : ((p : ℕ) : O) ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field O
  rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl]

private abbrev _root_.V3SolH.πX : V3Glue.Site.XO p O ⟶ Spec (CommRingCat.of O) := V3Asm.πX p O
p2m_export "V3SolH" "πX"
private abbrev _root_.V3SolH.bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶ V3Glue.Site.XO p O := V3Asm.bc p O κ toκ
p2m_export "V3SolH" "bc"
private theorem _root_.V3SolH.bc_snd : bc p O κ toκ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) := V3Asm.bc_snd p O κ toκ

p2m_export "V3SolH" "bc_snd"
include p 𝔛 O hϖ κ toκ H

private abbrev _root_.V3SolH.R := V3Asm.R p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "R"
private abbrev _root_.V3SolH.C := V3Asm.C p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "C"
private abbrev _root_.V3SolH.D := V3Asm.D p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "D"
private abbrev _root_.V3SolH.Y := V3Asm.Y p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "Y"
private abbrev _root_.V3SolH.toDR := V3Asm.toDR p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "toDR"
private abbrev _root_.V3SolH.toBase := V3Asm.toBase p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "toBase"
theorem toDR_over : toDR p 𝔛 O hϖ κ toκ H ≫ pullback.snd _ _ = toBase p 𝔛 O hϖ κ toκ H := rfl
private theorem _root_.V3SolH.hq : ∀ n (y : (D p 𝔛 O hϖ κ toκ H).Y n), (((D p 𝔛 O hϖ κ toκ H).q n).base y).1 ∈ (D p 𝔛 O hϖ κ toκ H).X0 → y ∈ Set.range ((D p 𝔛 O hϖ κ toκ H).j n).base :=
  V3Asm.hq p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "hq"
private theorem _root_.V3SolH.mem_X0_iff (x : V3Glue.Site.XO p O) : x ∈ (D p 𝔛 O hϖ κ toκ H).X0 ↔ ∀ n, x ≠ V3Glue.Site.xpt 𝔛 (V3Asm.bc p O κ toκ) n :=
  V3Asm.mem_X0_iff p 𝔛 O κ toκ hϖ H x
p2m_export "V3SolH" "mem_X0_iff"
private abbrev _root_.V3SolH.width := V3Asm.width p 𝔛 O κ toκ hϖ H

p2m_export "V3SolH" "width"
local notation "𝕎" => width p 𝔛 O hϖ κ toκ H
local notation "𝕐" => Y p 𝔛 O hϖ κ toκ H

private theorem _root_.V3SolH.one_le_width : ∀ n, 1 ≤ width p 𝔛 O hϖ κ toκ H n := V3Asm.one_le_width p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "one_le_width"
private theorem _root_.V3SolH.hRF : ∀ n, IsIso (((C p 𝔛 O hϖ κ toκ H).f n).residueFieldMap ((C p 𝔛 O hϖ κ toκ H).xU n)) := V3Asm.hRF p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "hRF"
theorem isClosed_xpt (n : V3Glue.Site.Node p 𝔛 κ) : IsClosed ({V3Glue.Site.xpt 𝔛 (V3Asm.bc p O κ toκ) n} : Set (V3Glue.Site.XO p O)) :=
  H.hxcl n
theorem etale_f (n : V3Glue.Site.Node p 𝔛 κ) : Etale ((C p 𝔛 O hϖ κ toκ H).f n) := (C p 𝔛 O hϖ κ toκ H).f_etale n
private abbrev _root_.V3SolH.chartIso := V3Asm.chartIso p 𝔛 O κ toκ hϖ H
p2m_export "V3SolH" "chartIso"

private theorem _root_.V3SolH.isReduced_Y (n : V3Glue.Site.Node p 𝔛 κ) : IsReduced ((D p 𝔛 O hϖ κ toκ H).Y n) := by
  haveI : IsReduced ((C p 𝔛 O hϖ κ toκ H).Res n) := MvPolynomial.CrossingQuotient.Resolution.isReduced
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hϖ) _
  exact V3Glue.ChartInput.isReduced_Y (C p 𝔛 O hϖ κ toκ H) n

p2m_export "V3SolH" "isReduced_Y"
private theorem _root_.V3SolH.chartIso_hom_fst (n : V3Glue.Site.Node p 𝔛 κ) : (chartIso p 𝔛 O hϖ κ toκ H n).hom ≫ (toDR p 𝔛 O hϖ κ toκ H ∣_ (C p 𝔛 O hϖ κ toκ H).U n) = (C p 𝔛 O hϖ κ toκ H).q n :=
  V3Asm.chartIso_hom_fst p 𝔛 O κ toκ hϖ H n

p2m_export "V3SolH" "chartIso_hom_fst"
theorem isProper_πX : IsProper (πX p O) := by
  haveI := 𝔛.isProper
  exact MorphismProperty.pullback_snd _ _ inferInstance

theorem flat_πX : Flat (πX p O) := by
  haveI := 𝔛.flat
  exact MorphismProperty.pullback_snd _ _ inferInstance

theorem toDR_proper : IsProper (toDR p 𝔛 O hϖ κ toκ H) :=
  (D p 𝔛 O hϖ κ toκ H).isProper_toDR (hq p 𝔛 O hϖ κ toκ H)
    (fun n => by show IsProper ((V3Asm.C p 𝔛 O κ toκ hϖ H).q n); infer_instance)

private theorem _root_.V3SolH.isProper : IsProper (toBase p 𝔛 O hϖ κ toκ H) := by
  haveI := toDR_proper p 𝔛 O hϖ κ toκ H
  haveI := isProper_πX p 𝔛 O hϖ κ toκ H
  show IsProper (V3Asm.toDR p 𝔛 O κ toκ hϖ H ≫ V3Asm.πX p O)
  infer_instance

p2m_export "V3SolH" "isProper"

private theorem _root_.V3SolH.flat : Flat (toBase p 𝔛 O hϖ κ toκ H) := by
  haveI := flat_πX p 𝔛 O hϖ κ toκ H
  exact (D p 𝔛 O hϖ κ toκ H).flat_toDR_comp (πX p O) (fun n => (C p 𝔛 O hϖ κ toκ H).flat_q_ι_πX n)

p2m_export "V3SolH" "flat"
omit 𝔛 κ toκ H in

theorem isIntegral_XO : IsIntegral (V3Glue.Site.XO p O) :=
  ModularCurve.DRModel.isIntegral_pullback_toBase p O hϖ

omit hϖ κ toκ H in

theorem isLocallyNoetherian_XO : IsLocallyNoetherian (V3Glue.Site.XO p O) := by
  haveI := ModularCurve.DRModelPackage.locallyOfFinitePresentation_toBase p 𝔛
  exact LocallyOfFiniteType.isLocallyNoetherian (πX p O)

theorem snd_preimage_basicOpen_le_X0 :
    pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) ≤
      (D p 𝔛 O hϖ κ toκ H).X0 := by
  intro x hx
  refine (mem_X0_iff p 𝔛 O hϖ κ toκ H x).mpr fun n hn => ?_
  subst hn
  exact DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _ hx

theorem nonempty_X0 : Nonempty ((D p 𝔛 O hϖ κ toκ H).X0) := by
  haveI := isIntegral_XO p O hϖ
  haveI := flat_πX p 𝔛 O hϖ κ toκ H
  obtain ⟨x⟩ := (inferInstance : Nonempty ↥(V3Glue.Site.XO p O))
  let ξ : ↥(Spec (CommRingCat.of O)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ : ξ ⤳ (πX p O).base x := (PrimeSpectrum.le_iff_specializes ξ ((πX p O).base x)).mp bot_le
  obtain ⟨x', -, hx'⟩ := Flat.generalizingMap (πX p O) hξ
  refine ⟨⟨x', snd_preimage_basicOpen_le_X0 p 𝔛 O hϖ κ toκ H ?_⟩⟩
  show (πX p O).base x' ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O)
  rw [show (πX p O).base x' = ξ from hx']
  show ((p : ℕ) : O) ∉ (⊥ : Ideal O)
  rw [Ideal.mem_bot]
  exact p_ne_zero p O hϖ

theorem isIntegral : IsIntegral (Y p 𝔛 O hϖ κ toκ H) := by
  haveI := isIntegral_XO p O hϖ
  haveI := nonempty_X0 p 𝔛 O hϖ κ toκ H
  exact (D p 𝔛 O hϖ κ toκ H).isIntegral_glued' (hq p 𝔛 O hϖ κ toκ H)
    (fun n => isClosed_xpt p 𝔛 O hϖ κ toκ H n)
    (fun n => (C p 𝔛 O hϖ κ toκ H).interior_setOf_q_eq n)
    (fun n => isReduced_Y p 𝔛 O hϖ κ toκ H n)

private theorem _root_.V3SolH.isLocallyNoetherian : IsLocallyNoetherian (Y p 𝔛 O hϖ κ toκ H) := by
  haveI := isLocallyNoetherian_XO p 𝔛 O
  exact (D p 𝔛 O hϖ κ toκ H).isLocallyNoetherian_glued
    (fun n => by show IsLocallyNoetherian ((V3Asm.C p 𝔛 O κ toκ hϖ H).Y n); infer_instance)

p2m_export "V3SolH" "isLocallyNoetherian"
omit 𝔛 κ toκ H in
include hϖ in

theorem irreducible_p : Irreducible ((p : ℕ) : O) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hϖ

theorem hResDim : ∀ n (z : (C p 𝔛 O hϖ κ toκ H).Res n), ringKrullDim (((C p 𝔛 O hϖ κ toκ H).Res n).presheaf.stalk z) ≤ 2 :=
  fun n z => MvPolynomial.CrossingQuotient.Resolution.ringKrullDim_stalk_le_two (irreducible_p p O hϖ) _ z

theorem hRes : ∀ n (z : (C p 𝔛 O hϖ κ toκ H).Res n),
    IsRegularLocalRing (((C p 𝔛 O hϖ κ toκ H).Res n).presheaf.stalk z) ∧
      ringKrullDim (((C p 𝔛 O hϖ κ toκ H).Res n).presheaf.stalk z) ≤ 2 :=
  fun n z => ⟨MvPolynomial.CrossingQuotient.Resolution.isRegularLocalRing_stalk (irreducible_p p O hϖ) _ z, hResDim p 𝔛 O hϖ κ toκ H n z⟩

theorem hX : ∀ x : V3Glue.Site.XO p O, x ∈ (C p 𝔛 O hϖ κ toκ H).X0 →
    x ∉ (πX p O) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    IsRegularLocalRing ((V3Glue.Site.XO p O).presheaf.stalk x) ∧ ringKrullDim ((V3Glue.Site.XO p O).presheaf.stalk x) ≤ 2 :=
  fun x hx hz => ⟨DRModelPackage.isRegularLocalRing_stalk_of_forall_ne_baseChangeMap_crossing p 𝔛 O hϖ κ toκ x hz
      ((mem_X0_iff p 𝔛 O hϖ κ toκ H x).mp hx),
    DRModelPackage.ringKrullDim_stalk_pullback_toBase_le_two p 𝔛 O x⟩

theorem regular_and_dim (y : Y p 𝔛 O hϖ κ toκ H)
    (hy : y ∉ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    IsRegularLocalRing ((Y p 𝔛 O hϖ κ toκ H).presheaf.stalk y) ∧ ringKrullDim ((Y p 𝔛 O hϖ κ toκ H).presheaf.stalk y) ≤ 2 := by
  haveI : ∀ n, Etale ((C p 𝔛 O hϖ κ toκ H).f n) := etale_f p 𝔛 O hϖ κ toκ H
  exact (C p 𝔛 O hϖ κ toκ H).isRegularLocalRing_stalk_glued_and_ringKrullDim_le_two' (hRes p 𝔛 O hϖ κ toκ H)
    (fun x => x ∉ (πX p O) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (hX p 𝔛 O hϖ κ toκ H) y hy

theorem regular : ∀ y : Y p 𝔛 O hϖ κ toκ H, y ∉ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    IsRegularLocalRing ((Y p 𝔛 O hϖ κ toκ H).presheaf.stalk y) :=
  fun y hy => (regular_and_dim p 𝔛 O hϖ κ toκ H y hy).1

theorem stalk_dim_le_two : ∀ y : Y p 𝔛 O hϖ κ toκ H, y ∉ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) →
    ringKrullDim ((Y p 𝔛 O hϖ κ toκ H).presheaf.stalk y) ≤ 2 :=
  fun y hy => (regular_and_dim p 𝔛 O hϖ κ toκ H y hy).2

theorem fst_preimage_smoothLocus_le_X0 :
    pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus ≤
      (D p 𝔛 O hϖ κ toκ H).X0 := by
  intro x hx
  refine (mem_X0_iff p 𝔛 O hϖ κ toκ H x).mpr fun n hn => ?_
  subst hn
  set y := (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base n with hy
  have hyboth : y ∈ Set.range ⇑(𝔛.compInf κ).base ∧ y ∈ Set.range ⇑(𝔛.compZero κ).base := by
    refine ⟨⟨(pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n, rfl⟩,
      ⟨(pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n, ?_⟩⟩
    rw [hy, pullback.condition]
    rfl
  apply (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
    p 𝔛 κ y).not.mpr (not_not.mpr hyboth)
  have hfst : DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = pullback.fst (DRModel.toBase p) _ := by
    rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  change (pullback.fst (DRModel.toBase p) _).base y ∈ 𝔛.smoothLocus
  rw [← hfst]
  exact hx

theorem toDR_iso_smoothLocus :
    IsIso (toDR p 𝔛 O hϖ κ toκ H ∣_ (pullback.fst (DRModel.toBase p) _ ⁻¹ᵁ 𝔛.smoothLocus)) :=
  (D p 𝔛 O hϖ κ toκ H).isIso_toDR_restrict (hq p 𝔛 O hϖ κ toκ H) (fst_preimage_smoothLocus_le_X0 p 𝔛 O hϖ κ toκ H)

theorem toDR_iso_generic :
    IsIso (toDR p 𝔛 O hϖ κ toκ H ∣_ (pullback.snd (DRModel.toBase p) _ ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))) :=
  (D p 𝔛 O hϖ κ toκ H).isIso_toDR_restrict (hq p 𝔛 O hϖ κ toκ H) (snd_preimage_basicOpen_le_X0 p 𝔛 O hϖ κ toκ H)

omit 𝔛 κ toκ H in
include hϖ in

private theorem _root_.V3SolH.p_mem_maximalIdeal : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O :=
  hϖ ▸ Ideal.mem_span_singleton_self _

p2m_export "V3SolH" "p_mem_maximalIdeal"

theorem hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (C p 𝔛 O hϖ κ toκ H).X0 := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact fst_preimage_smoothLocus_le_X0 p 𝔛 O hϖ κ toκ H
      (DRModelPackage.baseChangeMap_genericPoint_mem_preimage_smoothLocus p 𝔛 O κ toκ).1
  · have hi : i = 0 := Fin.eq_zero i
    subst hi
    exact fst_preimage_smoothLocus_le_X0 p 𝔛 O hϖ κ toκ H
      (DRModelPackage.baseChangeMap_genericPoint_mem_preimage_smoothLocus p 𝔛 O κ toκ).2

private abbrev _root_.V3SolH.comp := V3Asm.comp p 𝔛 O κ toκ hϖ H (hξ p 𝔛 O hϖ κ toκ H)
p2m_export "V3SolH" "comp"
private abbrev _root_.V3SolH.η := V3Asm.η p 𝔛 O κ toκ hϖ H (hξ p 𝔛 O hϖ κ toκ H)
p2m_export "V3SolH" "η"
private abbrev _root_.V3SolH.edgePt := V3Asm.edgePt p 𝔛 O κ toκ hϖ H

p2m_export "V3SolH" "edgePt"

theorem comp_integral : ∀ v, IsIntegral (comp p 𝔛 O hϖ κ toκ H v).subscheme := fun v => by
  show IsIntegral (Scheme.IdealSheafData.vanishingIdeal ⟨closure {(C p 𝔛 O hϖ κ toκ H).ηG (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) (hξ p 𝔛 O hϖ κ toκ H) v}, isClosed_closure⟩).subscheme
  exact Scheme.isIntegral_subscheme_vanishingIdeal _ isIrreducible_singleton.closure

omit hϖ H in

theorem πX_bc_notMem_basicOpen (w : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))) :
    (πX p O).base ((bc p O κ toκ).base w) ∉
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  have h := congr($(bc_snd p O κ toκ).base w)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [h]
  intro hmem
  apply (PrimeSpectrum.mem_basicOpen _ _).mp hmem
  show ((p : ℕ) : O) ∈ Ideal.comap toκ _
  rw [Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]
  exact zero_mem _

theorem exists_toDR_η_eq_bc (v : X0MqComponents 𝕎) :
    ∃ w, (toDR p 𝔛 O hϖ κ toκ H).base (η p 𝔛 O hϖ κ toκ H v) = (bc p O κ toκ).base w := by
  rcases v with j | ⟨n, k⟩
  · have h0 : ∀ z : (C p 𝔛 O hϖ κ toκ H).X0, (toDR p 𝔛 O hϖ κ toκ H).base ((D p 𝔛 O hϖ κ toκ H).ιX0.base z) = z.1 := fun z => by
      have := congr($((D p 𝔛 O hϖ κ toκ H).ιX0_toDR).base z)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      exact this.trans (by simp)
    show ∃ w, (toDR p 𝔛 O hϖ κ toκ H).base ((D p 𝔛 O hϖ κ toκ H).ιX0.base ⟨V3Asm.ξ p 𝔛 O κ toκ j, hξ p 𝔛 O hϖ κ toκ H j⟩) = _
    rw [h0]
    refine Fin.cases ?_ (fun i => ?_) j
    · exact ⟨(𝔛.compInf κ).base (genericPoint (𝔛.ratModel κ).C), rfl⟩
    · have hi : i = 0 := Fin.eq_zero i
      subst hi
      exact ⟨(𝔛.compZero κ).base (genericPoint (𝔛.ratModel κ).C), rfl⟩
  · refine ⟨(𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n), ?_⟩
    show (V3Asm.C p 𝔛 O κ toκ hϖ H).toGlueInput.toDR.base ((C p 𝔛 O hϖ κ toκ H).exPt n (hRF p 𝔛 O hϖ κ toκ H n) _ _) = _
    rw [(C p 𝔛 O hϖ κ toκ H).toDR_exPt]
    rfl

theorem η_not_mem : ∀ v, η p 𝔛 O hϖ κ toκ H v ∉ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ
    (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  intro v hv
  obtain ⟨w, hw⟩ := exists_toDR_η_eq_bc p 𝔛 O hϖ κ toκ H v
  apply πX_bc_notMem_basicOpen p 𝔛 O κ toκ w
  rw [← hw]
  exact hv

theorem comp_support : ∀ v (y : 𝕐), y ∈ (comp p 𝔛 O hϖ κ toκ H v).support →
    y ∉ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) :=
  fun v y hy => (C p 𝔛 O hϖ κ toκ H).apply_not_mem_of_mem_support_compG (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) (hξ p 𝔛 O hϖ κ toκ H) (toBase p 𝔛 O hϖ κ toκ H)
    (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) v (η_not_mem p 𝔛 O hϖ κ toκ H v) y hy

theorem exists_mem_preimage_basicOpen : ∃ y : 𝕐, y ∈ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ
    (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  haveI := isIntegral_XO p O hϖ
  haveI := flat_πX p 𝔛 O hϖ κ toκ H
  obtain ⟨x⟩ := (inferInstance : Nonempty ↥(V3Glue.Site.XO p O))
  let ξ0 : ↥(Spec (CommRingCat.of O)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ0 : ξ0 ⤳ (πX p O).base x := (PrimeSpectrum.le_iff_specializes ξ0 ((πX p O).base x)).mp bot_le
  obtain ⟨x', -, hx'⟩ := Flat.generalizingMap (πX p O) hξ0
  have hx'D : x' ∈ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
    show (πX p O).base x' ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O)
    rw [show (πX p O).base x' = ξ0 from hx']
    show ((p : ℕ) : O) ∉ (⊥ : Ideal O)
    rw [Ideal.mem_bot]
    exact p_ne_zero p O hϖ
  refine ⟨(D p 𝔛 O hϖ κ toκ H).ιX0.base ⟨x', snd_preimage_basicOpen_le_X0 p 𝔛 O hϖ κ toκ H hx'D⟩, ?_⟩
  show (toBase p 𝔛 O hϖ κ toκ H).base ((D p 𝔛 O hϖ κ toκ H).ιX0.base _) ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O)
  have e1 := congr($((C p 𝔛 O hϖ κ toκ H).ιX0_toBase).base ⟨x', snd_preimage_basicOpen_le_X0 p 𝔛 O hϖ κ toκ H hx'D⟩)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e1
  erw [e1]
  (first | exact hx'D | simpa using hx'D | (have h__ := hx'D; simp at h__; exact h__))

theorem preimage_basicOpen_eq : (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) =
    (𝕐).basicOpen ((p : ℕ) : Γ(𝕐, ⊤)) := by
  have e : (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) =
      (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((p : ℕ) : O)) :=
    (basicOpen_eq_of_affine _).symm
  rw [e, Scheme.preimage_basicOpen, map_natCast, map_natCast]
  try rfl

theorem preimage_basicOpen_eq' : (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) =
    (𝕐).basicOpen ((p : ℕ) : Γ(𝕐, ⊤)) := by
  have e : (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) =
      (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((p : ℕ) : O)) :=
    (basicOpen_eq_of_affine _).symm
  rw [e, Scheme.preimage_basicOpen_top, map_natCast, map_natCast]

theorem natCast_Γ_ne_zero : ((p : ℕ) : Γ(𝕐, ⊤)) ≠ 0 := by
  intro h0
  obtain ⟨y, hy⟩ := exists_mem_preimage_basicOpen p 𝔛 O hϖ κ toκ H
  rw [preimage_basicOpen_eq, h0, Scheme.basicOpen_zero] at hy
  exact hy

theorem η_max (v : X0MqComponents 𝕎) (y : 𝕐) (hy : y ⤳ η p 𝔛 O hϖ κ toκ H v)
    (hyp : y ∉ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    y = η p 𝔛 O hϖ κ toκ H v := by
  haveI : IsLocalRing O := inferInstance
  rcases v with j | ⟨n, k⟩
  · refine (C p 𝔛 O hϖ κ toκ H).ηG_inl_eq_of_specializes (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H)
      (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) (hξ p 𝔛 O hϖ κ toκ H) j
      (fun z => z ∉ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
      (fun x' => (πX p O).base x'.1 ∉ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
      ?_ ?_ y hy hyp
    · intro x' hP hQ
      apply hP
      show (toBase p 𝔛 O hϖ κ toκ H).base (((D p 𝔛 O hϖ κ toκ H).ιX0).base x') ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O)
      have e1 := congr($((C p 𝔛 O hϖ κ toκ H).ιX0_toBase).base x')
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e1
      erw [e1]
      (first | exact hQ | simpa using hQ | (have h__ := hQ; simp at h__; exact h__))
    · intro x' hsp hQ
      apply Subtype.ext
      have hsp' : (x' : V3Glue.Site.XO p O) ⤳ V3Asm.ξ p 𝔛 O κ toκ j := hsp.map continuous_subtype_val
      have hQ' : (x' : V3Glue.Site.XO p O) ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := hQ
      obtain ⟨h0, h1⟩ := ModularCurve.DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes p 𝔛 O hϖ κ toκ
      revert hsp'
      refine Fin.cases ?_ (fun i => ?_) j
      · intro hsp'
        exact h0 _ hQ' hsp'
      · intro hsp'
        have hi : i = 0 := Fin.eq_zero i
        subst hi
        exact h1 _ hQ' hsp'
  · haveI : (Ideal.span {((p : ℕ) : O)}).IsMaximal := hϖ ▸ inferInstance
    refine (C p 𝔛 O hϖ κ toκ H).ηG_inr_eq_of_specializes (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H)
      (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) (hξ p 𝔛 O hϖ κ toκ H) n k
      (fun z => z ∉ (toBase p 𝔛 O hϖ κ toκ H) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
      (fun o => o ∉ MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O hϖ κ toκ H).thick n) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
      ?_ ?_ y hy hyp
    · intro y' hP hQ
      apply hP
      show (toBase p 𝔛 O hϖ κ toκ H).base (((D p 𝔛 O hϖ κ toκ H).ιY n).base y') ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O)
      have e1 := congr($((C p 𝔛 O hϖ κ toκ H).ιY_toBase n).base y')
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e1
      erw [e1]
      exact hQ
    · intro o' ho' hQ
      have hU : MvPolynomial.CrossingQuotient.lineUIdeal ((p : ℕ) : O) (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) =
          Ideal.span {MvPolynomial.CrossingQuotient.U ((p : ℕ) : O)} := by
        rw [MvPolynomial.CrossingQuotient.lineUIdeal_eq_span_sup_map, hϖ, Ideal.map_span, Set.image_singleton]
        refine sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
        exact MvPolynomial.CrossingQuotient.algebraMap_mem_span_U ((p : ℕ) : O)
      exact MvPolynomial.CrossingQuotient.Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen
        ((p : ℕ) : O) ((C p 𝔛 O hϖ κ toκ H).thick n) _ _ (Or.inl hU) o' ho' hQ

theorem η_injective : Function.Injective (η p 𝔛 O hϖ κ toκ H) := by
  haveI : IsLocalRing O := inferInstance
  refine (C p 𝔛 O hϖ κ toκ H).ηG_injective (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H)
    (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) (hξ p 𝔛 O hϖ κ toκ H) ?_ ?_
  · exact ModularCurve.DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint p 𝔛 O hϖ κ toκ
  · intro n k k' h
    have h' : MvPolynomial.CrossingQuotient.Resolution.lineUGen ((p : ℕ) : O) ((C p 𝔛 O hϖ κ toκ H).thick n)
        (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) ⟨(k : ℕ), Nat.lt_of_lt_pred k.2⟩ =
      MvPolynomial.CrossingQuotient.Resolution.lineUGen ((p : ℕ) : O) ((C p 𝔛 O hϖ κ toκ H).thick n)
        (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) ⟨(k' : ℕ), Nat.lt_of_lt_pred k'.2⟩ := h
    exact Fin.ext (Fin.mk.inj_iff.mp (MvPolynomial.CrossingQuotient.Resolution.lineUGen_injective _ _ _ _ h'))

theorem exc_image : ∀ (n : V3Glue.Site.Node p 𝔛 κ) (i : Fin (𝕎 n - 1)), ∀ y ∈ (comp p 𝔛 O hϖ κ toκ H (Sum.inr ⟨n, i⟩)).support,
    (toDR p 𝔛 O hϖ κ toκ H).base y = (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base ((Equiv.refl _) n) :=
  fun n i y hy => (C p 𝔛 O hϖ κ toκ H).exc_image' (V3Asm.hRF p 𝔛 O κ toκ hϖ H) (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) (hξ p 𝔛 O hϖ κ toκ H) (isClosed_xpt p 𝔛 O hϖ κ toκ H) n i y hy

theorem edgePt_over : ∀ (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin (𝕎 n)),
    (toDR p 𝔛 O hϖ κ toκ H).base (edgePt p 𝔛 O hϖ κ toκ H n d) =
      (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base ((Equiv.refl _) n) :=
  fun n d => (C p 𝔛 O hϖ κ toκ H).toDR_edgePt' (hRF p 𝔛 O hϖ κ toκ H) (V3Asm.oRes p 𝔛 O κ toκ hϖ H) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H) n d

theorem edgePt_injective : Function.Injective (fun e : Σ n, Fin (𝕎 n) => edgePt p 𝔛 O hϖ κ toκ H e.1 e.2) :=
  (C p 𝔛 O hϖ κ toκ H).edgePt'_injective (hRF p 𝔛 O hϖ κ toκ H) (V3Asm.oRes p 𝔛 O κ toκ hϖ H) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H)
    (fun n => MvPolynomial.CrossingQuotient.Resolution.origin_injective ((p : ℕ) : O) ((C p 𝔛 O hϖ κ toκ H).thick n) (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ))

end V3SolH
p2m_reactivate "P2MW.S_V3Asm_comp_isInvertible.MvPolynomial P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme P2MW.S_V3Asm_comp_isInvertible.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_V3Asm_comp_isInvertible.V3Glue P2MW.S_V3Asm_comp_isInvertible.V3Glue.ChartInput P2MW.S_V3Asm_comp_isInvertible.MvPolynomial.CrossingQuotient.Resolution"

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : ModularCurve.DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (H : V3Asm.SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) :
    ∀ v, (V3Asm.comp p 𝔛 O κ toκ hϖ H hξ v).IsInvertible := by
  intro v
  haveI := V3SolH.isLocallyNoetherian p 𝔛 O hϖ κ toκ H
  haveI := V3SolH.isIntegral p 𝔛 O hϖ κ toκ H
  have hη : ringKrullDim ((V3Asm.Y p 𝔛 O κ toκ hϖ H).presheaf.stalk (V3Asm.η p 𝔛 O κ toκ hϖ H hξ v)) = 1 := by
    refine AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen
      ((p : ℕ) : Γ(V3Asm.Y p 𝔛 O κ toκ hϖ H, ⊤)) (V3SolH.natCast_Γ_ne_zero p 𝔛 O hϖ κ toκ H) _ ?_ ?_
    · rw [← V3SolH.preimage_basicOpen_eq]
      exact V3SolH.η_not_mem p 𝔛 O hϖ κ toκ H v
    · intro y hy hyt
      rw [← V3SolH.preimage_basicOpen_eq] at hyt
      exact V3SolH.η_max p 𝔛 O hϖ κ toκ H v y hy hyt
  show (Scheme.IdealSheafData.vanishingIdeal ⟨closure {V3Asm.η p 𝔛 O κ toκ hϖ H hξ v}, isClosed_closure⟩).IsInvertible
  refine AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing _ hη ?_
  intro y hy
  have hy' : y ∈ ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ v).support : Set (V3Asm.Y p 𝔛 O κ toκ hϖ H)) := by
    erw [V3Asm.comp_def, V3Glue.ChartInput.coe_support_compG]
    exact hy
  exact V3SolH.regular_and_dim p 𝔛 O hϖ κ toκ H y (V3SolH.comp_support p 𝔛 O hϖ κ toκ H v y hy')

end
end S_V3Asm_comp_isInvertible
end P2MW
export P2MW.S_V3Asm_comp_isInvertible (solution)
