-- Prove2me | solution 1 for V3Asm.exists_smoothOffEdges
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5f7bd000-23a3-5a85-b008-e731be345ce2

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSite
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_preimage_smoothLocus_le_of_isPullback
import Theorems.Thm_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isProper_toCrossing
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Theorems.Thm_ModularCurve_DRModel_isIntegral_pullback_toBase
import Theorems.Thm_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Asm_exists_smoothOffEdges
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

namespace ModelSmooth

variable (R : Type u) [CommRing R]

example : Algebra.FinitePresentation R R[X] := inferInstance
example : Subsingleton (Algebra.H1Cotangent R R[X]) := inferInstance

noncomputable def kaehlerBasisPolynomial : Module.Basis Unit R[X] (Ω[R[X]⁄R]) :=
  (Module.Basis.singleton Unit R[X]).map (KaehlerDifferential.polynomialEquiv R).symm

theorem kaehlerBasisPolynomial_apply (i : Unit) : kaehlerBasisPolynomial R i = KaehlerDifferential.D R R[X] X := by
  simp [kaehlerBasisPolynomial, KaehlerDifferential.polynomialEquiv_symm]

theorem isStandardSmooth_polynomial : Algebra.IsStandardSmooth R R[X] :=
  Algebra.IsStandardSmooth.of_basis_kaehlerDifferential (kaehlerBasisPolynomial R) (by
    rintro _ ⟨i, rfl⟩
    exact ⟨X, (kaehlerBasisPolynomial_apply R i).symm⟩)

theorem isStandardSmoothOfRelativeDimension_one_polynomial [Nontrivial R] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R R[X] := by
  haveI := isStandardSmooth_polynomial R
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [rank_eq_card_basis (kaehlerBasisPolynomial R)]
  simp

theorem isStandardSmoothOfRelativeDimension_one_of_isLocalization_away_X [Nontrivial R] (S : Type u) [CommRing S]
    [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S] [IsLocalization.Away (X : R[X]) S] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R S := by
  haveI := isStandardSmoothOfRelativeDimension_one_polynomial R
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 R[X] S :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (X : R[X])
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 R R[X] S

end ModelSmooth

namespace MvPolynomial
p2m_export "MvPolynomial" "X map coeff R aeval_X ext support aeval_def algebraMap_apply comap algebraMap_eq C monomial coeff_zero sum_def notMem_support_iff aeval_C induction_on aeval CrossingQuotient.Resolution CrossingQuotient.Resolution.exists_ι_apply_eq CrossingQuotient.Resolution.toCrossing CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.Resolution.isProper_toCrossing"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.exists_ι_apply_eq Resolution.toCrossing Resolution.toSpec U V U_mul_V lift mk mk_surjective monomial monomial_natCast monomial_neg_natCast originIdeal linearIndependent_monomial_and_span_eq_top Resolution.isProper_toCrossing"
p2m_open "MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W)

noncomputable abbrev polyU : W[X] →ₐ[W] CrossingQuotient W t := Polynomial.aeval (U t)

noncomputable abbrev polyV : W[X] →ₐ[W] CrossingQuotient W t := Polynomial.aeval (V t)

theorem polyU_injective : Function.Injective (polyU t) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hli : LinearIndependent W (fun n : ℕ => monomial t (n : ℤ)) :=
    (linearIndependent_monomial_and_span_eq_top t).1.comp _ Nat.cast_injective
  have hsum : polyU t p = ∑ n ∈ p.support, p.coeff n • monomial t (n : ℤ) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [monomial_natCast]
    exact (Algebra.smul_def _ _).symm
  rw [hsum] at hp
  have h0 := linearIndependent_iff'.mp hli p.support (fun n => p.coeff n) hp
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n ∈ p.support
  · exact h0 n hn
  · exact Polynomial.notMem_support_iff.mp hn

theorem polyV_injective : Function.Injective (polyV t) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hli : LinearIndependent W (fun n : ℕ => monomial t (-(n : ℤ))) :=
    (linearIndependent_monomial_and_span_eq_top t).1.comp (fun n : ℕ => -(n : ℤ))
      (fun a b h => Nat.cast_injective (neg_injective h))
  have hsum : polyV t p = ∑ n ∈ p.support, p.coeff n • monomial t (-(n : ℤ)) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [monomial_neg_natCast]
    exact (Algebra.smul_def _ _).symm
  rw [hsum] at hp
  have h0 := linearIndependent_iff'.mp hli p.support (fun n => p.coeff n) hp
  ext n
  rw [Polynomial.coeff_zero]
  by_cases hn : n ∈ p.support
  · exact h0 n hn
  · exact Polynomial.notMem_support_iff.mp hn

theorem exists_mul_U_pow_eq_polyU (c : CrossingQuotient W t) : ∃ (n : ℕ) (q : W[X]), c * U t ^ n = polyU t q := by
  obtain ⟨f, rfl⟩ := mk_surjective t c
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, Polynomial.C a, by rw [pow_zero, mul_one, Polynomial.aeval_C]; exact (mk t).commutes a⟩
  | add p q hp hq =>
    obtain ⟨n₁, q₁, h₁⟩ := hp
    obtain ⟨n₂, q₂, h₂⟩ := hq
    refine ⟨n₁ + n₂, q₁ * Polynomial.X ^ n₂ + q₂ * Polynomial.X ^ n₁, ?_⟩
    rw [map_add, add_mul, map_add, map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_X, ← h₁, ← h₂]
    ring
  | mul_X p i hp =>
    obtain ⟨n, q, h⟩ := hp
    fin_cases i
    · refine ⟨n, q * Polynomial.X, ?_⟩
      rw [map_mul, map_mul, Polynomial.aeval_X, ← h]
      show mk t p * U t * U t ^ n = mk t p * U t ^ n * U t
      ring
    · refine ⟨n + 1, Polynomial.C t * q, ?_⟩
      rw [map_mul, map_mul, Polynomial.aeval_C, ← h]
      show mk t p * V t * U t ^ (n + 1) = algebraMap W _ t * (mk t p * U t ^ n)
      rw [pow_succ, ← U_mul_V]
      ring

theorem exists_mul_V_pow_eq_polyV (c : CrossingQuotient W t) : ∃ (n : ℕ) (q : W[X]), c * V t ^ n = polyV t q := by
  obtain ⟨f, rfl⟩ := mk_surjective t c
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, Polynomial.C a, by rw [pow_zero, mul_one, Polynomial.aeval_C]; exact (mk t).commutes a⟩
  | add p q hp hq =>
    obtain ⟨n₁, q₁, h₁⟩ := hp
    obtain ⟨n₂, q₂, h₂⟩ := hq
    refine ⟨n₁ + n₂, q₁ * Polynomial.X ^ n₂ + q₂ * Polynomial.X ^ n₁, ?_⟩
    rw [map_add, add_mul, map_add, map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_X, ← h₁, ← h₂]
    ring
  | mul_X p i hp =>
    obtain ⟨n, q, h⟩ := hp
    fin_cases i
    · refine ⟨n + 1, Polynomial.C t * q, ?_⟩
      rw [map_mul, map_mul, Polynomial.aeval_C, ← h]
      show mk t p * U t * V t ^ (n + 1) = algebraMap W _ t * (mk t p * V t ^ n)
      rw [pow_succ, ← U_mul_V]
      ring
    · refine ⟨n, q * Polynomial.X, ?_⟩
      rw [map_mul, map_mul, Polynomial.aeval_X, ← h]
      show mk t p * V t * V t ^ n = mk t p * V t ^ n * V t
      ring

section awayU

theorem isStandardSmoothOfRelativeDimension_one_awayU [Nontrivial W] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 W (Localization.Away (U t)) := by
  letI alg : Algebra W[X] (Localization.Away (U t)) :=
    ((algebraMap (CrossingQuotient W t) (Localization.Away (U t))).comp (polyU t).toRingHom).toAlgebra
  letI smulAlg : SMul W[X] (Localization.Away (U t)) := alg.toSMul
  have halg : ∀ q : W[X], algebraMap W[X] (Localization.Away (U t)) q =
      algebraMap (CrossingQuotient W t) _ (polyU t q) := fun q => rfl
  haveI : IsScalarTower W W[X] (Localization.Away (U t)) :=
    IsScalarTower.of_algebraMap_eq (R := W) (S := W[X]) (A := Localization.Away (U t)) fun w => by
      rw [halg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization.Away (Polynomial.X : W[X]) (Localization.Away (U t)) :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        rw [halg, map_pow, Polynomial.aeval_X, map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit (U t)).pow n
      surj := fun z => by
        obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (U t)) z
        obtain ⟨n, q, hq⟩ := exists_mul_U_pow_eq_polyU t c
        refine ⟨⟨q, ⟨Polynomial.X ^ (m + n), _, rfl⟩⟩, ?_⟩
        show IsLocalization.mk' _ c ⟨U t ^ m, _⟩ * algebraMap W[X] _ (Polynomial.X ^ (m + n)) = algebraMap W[X] _ q
        rw [halg, halg, map_pow, Polynomial.aeval_X, pow_add, map_mul, ← mul_assoc,
          IsLocalization.mk'_spec _ c ⟨U t ^ m, _⟩, ← map_mul, hq]
      exists_of_eq := fun {p q} h => by
        rw [halg, halg] at h
        obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (U t)) h
        refine ⟨⟨Polynomial.X ^ k, k, rfl⟩, polyU_injective t ?_⟩
        simpa only [map_mul, map_pow, Polynomial.aeval_X] using hk }
  exact ModelSmooth.isStandardSmoothOfRelativeDimension_one_of_isLocalization_away_X W (Localization.Away (U t))

end awayU

section awayV

theorem isStandardSmoothOfRelativeDimension_one_awayV [Nontrivial W] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 W (Localization.Away (V t)) := by
  letI alg : Algebra W[X] (Localization.Away (V t)) :=
    ((algebraMap (CrossingQuotient W t) (Localization.Away (V t))).comp (polyV t).toRingHom).toAlgebra
  letI smulAlg : SMul W[X] (Localization.Away (V t)) := alg.toSMul
  have halg : ∀ q : W[X], algebraMap W[X] (Localization.Away (V t)) q =
      algebraMap (CrossingQuotient W t) _ (polyV t q) := fun q => rfl
  haveI : IsScalarTower W W[X] (Localization.Away (V t)) :=
    IsScalarTower.of_algebraMap_eq (R := W) (S := W[X]) (A := Localization.Away (V t)) fun w => by
      rw [halg, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization.Away (Polynomial.X : W[X]) (Localization.Away (V t)) :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        rw [halg, map_pow, Polynomial.aeval_X, map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit (V t)).pow n
      surj := fun z => by
        obtain ⟨⟨c, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (V t)) z
        obtain ⟨n, q, hq⟩ := exists_mul_V_pow_eq_polyV t c
        refine ⟨⟨q, ⟨Polynomial.X ^ (m + n), _, rfl⟩⟩, ?_⟩
        show IsLocalization.mk' _ c ⟨V t ^ m, _⟩ * algebraMap W[X] _ (Polynomial.X ^ (m + n)) = algebraMap W[X] _ q
        rw [halg, halg, map_pow, Polynomial.aeval_X, pow_add, map_mul, ← mul_assoc,
          IsLocalization.mk'_spec _ c ⟨V t ^ m, _⟩, ← map_mul, hq]
      exists_of_eq := fun {p q} h => by
        rw [halg, halg] at h
        obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (V t)) h
        refine ⟨⟨Polynomial.X ^ k, k, rfl⟩, polyV_injective t ?_⟩
        simpa only [map_mul, map_pow, Polynomial.aeval_X] using hk }
  exact ModelSmooth.isStandardSmoothOfRelativeDimension_one_of_isLocalization_away_X W (Localization.Away (V t))

end awayV

end MvPolynomial.CrossingQuotient

namespace MvPolynomial
p2m_export "MvPolynomial" "X map coeff R aeval_X ext support aeval_def algebraMap_apply comap algebraMap_eq C monomial coeff_zero sum_def notMem_support_iff aeval_C induction_on aeval CrossingQuotient.Resolution CrossingQuotient.Resolution.exists_ι_apply_eq CrossingQuotient.Resolution.toCrossing CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.Resolution.isProper_toCrossing"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.exists_ι_apply_eq Resolution.toCrossing Resolution.toSpec U V U_mul_V lift mk mk_surjective monomial monomial_natCast monomial_neg_natCast originIdeal linearIndependent_monomial_and_span_eq_top Resolution.isProper_toCrossing"
p2m_open "MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W)

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry TopologicalSpace"

noncomputable section

private abbrev _root_.MvPolynomial.CrossingQuotient.D {R : Type u} [CommRing R] (g : R) : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen g

p2m_export "MvPolynomial.CrossingQuotient" "D"

theorem smoothOfRelativeDimension_one_basicOpen_ι_comp {R : Type u} [CommRing R] [Algebra W R] (g : R)
    (h : Algebra.IsStandardSmoothOfRelativeDimension 1 W (Localization.Away g)) :
    SmoothOfRelativeDimension 1
      ((D g).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap W R))) := by
  let u : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
  let eI := IsOpenImmersion.isoOfRangeEq u (D g).ι
    (by rw [Scheme.Opens.range_ι]; exact PrimeSpectrum.localization_away_comap_range (Localization.Away g) g)
  have hfac : (D g).ι = eI.inv ≫ u :=
    (IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _).symm
  haveI hu : SmoothOfRelativeDimension 1 (u ≫ Spec.map (CommRingCat.ofHom (algebraMap W R))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq W R (Localization.Away g)]
    refine HasRingHomProperty.Spec_iff.mpr ?_
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr h
  rw [hfac, Category.assoc]
  show SmoothOfRelativeDimension (0 + 1) (eI.inv ≫ u ≫ Spec.map (CommRingCat.ofHom (algebraMap W R)))
  infer_instance

theorem smoothOfRelativeDimension_one_basicOpen_U [Nontrivial W] :
    SmoothOfRelativeDimension 1
      ((D (U t)).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t)))) :=
  smoothOfRelativeDimension_one_basicOpen_ι_comp (U t) (isStandardSmoothOfRelativeDimension_one_awayU t)

theorem smoothOfRelativeDimension_one_basicOpen_V [Nontrivial W] :
    SmoothOfRelativeDimension 1
      ((D (V t)).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap W (CrossingQuotient W t)))) :=
  smoothOfRelativeDimension_one_basicOpen_ι_comp (V t) (isStandardSmoothOfRelativeDimension_one_awayV t)

namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq toCrossing toSpec ι_toSpec origin eq_origin_pt_of_mem isProper_toCrossing"
p2m_open "MvPolynomial.CrossingQuotient.Resolution"

variable (e : ℕ)

def offOrigins : (Resolution t e).Opens :=
  ⨆ i : Fin e, (ι t e i) ''ᵁ (D (U t) ⊔ D (V t))

theorem ι_apply_mem_offOrigins {i : Fin e} {y : chartScheme t} (hy : U t ∉ y.asIdeal ∨ V t ∉ y.asIdeal) :
    ι t e i y ∈ offOrigins t e :=
  Opens.mem_iSup.mpr ⟨i, y, hy, rfl⟩

theorem ι_apply_mem_offOrigins_of_not {i : Fin e} {y : chartScheme t} (hy : ¬ (U t ∈ y.asIdeal ∧ V t ∈ y.asIdeal)) :
    ι t e i y ∈ offOrigins t e :=
  ι_apply_mem_offOrigins t e (not_and_or.mp hy)

abbrev gen (b : Bool) : CrossingQuotient W t := cond b (U t) (V t)

theorem range_basicOpen_ι_ι_subset (i : Fin e) (b : Bool) :
    Set.range ((D (gen t b)).ι ≫ ι t e i) ⊆
      Set.range (offOrigins t e).ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  refine ι_apply_mem_offOrigins t e ?_
  cases b
  · exact Or.inr z.2
  · exact Or.inl z.2

def piece (i : Fin e) (b : Bool) :
    ((D (gen t b)) : Scheme.{u}) ⟶ (offOrigins t e : Scheme.{u}) :=
  IsOpenImmersion.lift (offOrigins t e).ι ((D (gen t b)).ι ≫ ι t e i)
    (range_basicOpen_ι_ι_subset t e i b)

@[reassoc]
theorem piece_ι (i : Fin e) (b : Bool) :
    piece t e i b ≫ (offOrigins t e).ι = (D (gen t b)).ι ≫ ι t e i :=
  IsOpenImmersion.lift_fac _ _ _

scoped instance (i : Fin e) (b : Bool) : IsOpenImmersion (piece t e i b) := by
  dsimp only [piece]; infer_instance

def offOriginsCover : (offOrigins t e : Scheme.{u}).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin e × Bool) _ (fun p => piece t e p.1 p.2) (by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨y, hy, rfl⟩ := hi
    have key : ∀ (b : Bool) (hb : y ∈ (D (gen t b))),
        ∃ z, (piece t e i b).base z = ⟨ι t e i y, hx⟩ := fun b hb => by
      refine ⟨⟨y, hb⟩, (offOrigins t e).ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, piece_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply]
    rcases hy with hU | hV
    · obtain ⟨z, hz⟩ := key true hU
      exact ⟨⟨i, true⟩, z, hz⟩
    · obtain ⟨z, hz⟩ := key false hV
      exact ⟨⟨i, false⟩, z, hz⟩)

theorem smoothOfRelativeDimension_one_offOrigins [Nontrivial W] :
    SmoothOfRelativeDimension 1 ((offOrigins t e).ι ≫ toSpec t e) := by
  refine IsZariskiLocalAtSource.of_openCover (offOriginsCover t e) fun p => ?_
  obtain ⟨i, b⟩ := p
  show SmoothOfRelativeDimension 1 (piece t e i b ≫ (offOrigins t e).ι ≫ toSpec t e)
  rw [piece_ι_assoc, ι_toSpec]
  cases b
  · exact smoothOfRelativeDimension_one_basicOpen_V t
  · exact smoothOfRelativeDimension_one_basicOpen_U t

end Resolution
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution"

end
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution"

end MvPolynomial.CrossingQuotient
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient"
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial"

section W6dGeneric

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift SmoothOfRelativeDimension.smooth Scheme.Hom.preimage_smoothLocus_eq SmoothOfRelativeDimension IsOpenImmersion.isoOfRangeEq_inv_fac IsProper morphismRestrict_ι Scheme.Opens.range_ι Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff IsZariskiLocalAtSource.of_openCover Scheme.Hom.smoothLocus Scheme.Pullback.range_fst isPullback_morphismRestrict LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Spec.map Scheme Smooth IsZariskiLocalAtSource IsOpenImmersion Scheme.Hom.comp_base Flat smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Hom.smoothLocus_eq_top HasRingHomProperty.Spec_iff HasRingHomProperty.iff_of_source_openCover IsOpenImmersion.isoOfRangeEq Scheme.Cover.mkOfCovers Scheme.Hom.mem_smoothLocus Etale Scheme.Opens.ι_apply smoothOfRelativeDimension_comp Scheme.Opens smooth_isStableUnderBaseChange LocallyOfFinitePresentation Flat.generalizingMap Scheme.Pullback.exists_preimage_pullback HasRingHomProperty IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.Cover Scheme.ΓSpecIso smoothOfRelativeDimension_of_irreducibleSpace Scheme.Hom.smoothLocus_le_preimage_of_isPullback Scheme.Hom.preimage_smoothLocus_le_of_isPullback"
p2m_open "AlgebraicGeometry"

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.preimage_smoothLocus_eq Opens.range_ι Hom mk Hom.smoothLocus_eq_top_iff Γ Hom.smoothLocus Pullback.range_fst Hom.stalkMap_comp OpenCover Hom.comp_base affineCover Hom.smoothLocus_eq_top basicOpen Cover.mkOfCovers Hom.mem_smoothLocus Opens.ι_apply Opens residue le_iff_specializes Pullback.exists_preimage_pullback Hom.comp_apply Cover ΓSpecIso Hom.smoothLocus_le_preimage_of_isPullback Hom.preimage_smoothLocus_le_of_isPullback" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "image preimage_smoothLocus_eq isOpenEmbedding smoothLocus_eq_top_iff smoothLocus injective surjective mk stalkMap_comp stalkMap comp_base comp_app smoothLocus_eq_top cover residueFieldMap mem_smoothLocus ker comp_apply smoothLocus_le_preimage_of_isPullback preimage_smoothLocus_le_of_isPullback" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

scoped instance Scheme.Hom.smooth_smoothLocus_ι_comp [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
  intro x _
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact x.2

p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom"
namespace Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem _root_.AlgebraicGeometry.Scheme.Hom.le_smoothLocus_of_smooth [LocallyOfFinitePresentation f] (V : X.Opens) [Smooth (V.ι ≫ f)] :
    V ≤ f.smoothLocus := by
  intro x hx
  have h : (⟨x, hx⟩ : V) ∈ (V.ι ≫ f).smoothLocus := by rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at h
  exact h

end Scheme.Hom
p2m_export "AlgebraicGeometry" "Scheme.Hom.le_smoothLocus_of_smooth"
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.mem_smoothLocus_of_mem_of_smooth [LocallyOfFinitePresentation f] (V : X.Opens) (hV : Smooth (V.ι ≫ f))
    (x : X) (hx : x ∈ V) : x ∈ f.smoothLocus :=
  f.le_smoothLocus_of_smooth V hx

theorem smoothOfRelativeDimension_smoothLocus_ι_comp (n : ℕ) [LocallyOfFinitePresentation f] [IrreducibleSpace X]
    (V : X.Opens) (hV : (V : Set X).Nonempty) [SmoothOfRelativeDimension n (V.ι ≫ f)] :
    SmoothOfRelativeDimension n (f.smoothLocus.ι ≫ f) := by
  haveI : Smooth (V.ι ≫ f) := SmoothOfRelativeDimension.smooth n _
  have hle : V ≤ f.smoothLocus := f.le_smoothLocus_of_smooth V

  have hne : (f.smoothLocus : Set X).Nonempty := hV.mono hle
  haveI : IrreducibleSpace f.smoothLocus :=
    Subtype.irreducibleSpace ⟨hne, (IrreducibleSpace.isIrreducible_univ X).2.open_subset f.smoothLocus.2 (Set.subset_univ _)⟩

  let V' : (f.smoothLocus : Scheme.{u}).Opens := f.smoothLocus.ι ⁻¹ᵁ V
  have hV' : (V' : Set f.smoothLocus).Nonempty := by
    obtain ⟨x, hx⟩ := hV
    exact ⟨⟨x, hle hx⟩, hx⟩
  haveI : SmoothOfRelativeDimension n (V'.ι ≫ f.smoothLocus.ι ≫ f) := by
    have h : V'.ι ≫ f.smoothLocus.ι ≫ f = (f.smoothLocus.ι ∣_ V) ≫ (V.ι ≫ f) := by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    rw [h]
    have : SmoothOfRelativeDimension (0 + n) ((f.smoothLocus.ι ∣_ V) ≫ (V.ι ≫ f)) :=
      smoothOfRelativeDimension_comp 0 n (f := f.smoothLocus.ι ∣_ V) (V.ι ≫ f)
    simpa using this
  exact smoothOfRelativeDimension_of_irreducibleSpace n (f.smoothLocus.ι ≫ f) V' hV'

theorem locallyOfFinitePresentation_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType c] : LocallyOfFinitePresentation c := by
  have hft := (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType) (f := c) C.affineCover).mp
    inferInstance
  refine (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFinitePresentation) (f := c) C.affineCover).mpr
    fun i => ?_

  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  exact RingHom.FinitePresentation.of_finiteType.mp (hft i)

namespace Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

private theorem _root_.AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_comp_of_smooth {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) [Smooth g]
    [LocallyOfFinitePresentation h] (x : X) (hx : g.base x ∈ h.smoothLocus) :
    x ∈ (g ≫ h).smoothLocus := by
  rw [Scheme.Hom.mem_smoothLocus] at hx ⊢
  have hg : (g.stalkMap x).hom.FormallySmooth := by
    have : x ∈ g.smoothLocus := by rw [Scheme.Hom.smoothLocus_eq_top]; trivial
    exact this
  rw [Scheme.Hom.stalkMap_comp]
  change (CommRingCat.Hom.hom (g.stalkMap x) |>.comp (CommRingCat.Hom.hom (h.stalkMap (g.base x)))).FormallySmooth
  exact RingHom.FormallySmooth.comp hx hg

end Scheme.Hom
p2m_export "AlgebraicGeometry" "Scheme.Hom.mem_smoothLocus_comp_of_smooth"
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.mem_smoothLocus_of_fac {Z T : Scheme.{u}} (f : T ⟶ Z) [LocallyOfFinitePresentation f]
    (ι : X ⟶ T) [IsOpenImmersion ι] (g : X ⟶ Y) (h : Y ⟶ Z) [Smooth g] [LocallyOfFinitePresentation h]
    (fac : ι ≫ f = g ≫ h) (x : X) (hx : g.base x ∈ h.smoothLocus) :
    ι.base x ∈ f.smoothLocus := by
  have h1 : x ∈ (g ≫ h).smoothLocus := g.mem_smoothLocus_comp_of_smooth h x hx
  have h3 : x ∈ (ι ≫ f).smoothLocus := by
    have key : ∀ (k : X ⟶ Z) [LocallyOfFinitePresentation k], k = g ≫ h → x ∈ k.smoothLocus := by
      intro k _ hk; subst hk; exact h1
    exact key (ι ≫ f) fac
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at h3
  exact h3

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.mem_smoothLocus_of_fac' {Z T : Scheme.{u}} (f : T ⟶ Z) (hf : LocallyOfFinitePresentation f)
    (ι : X ⟶ T) (hι : IsOpenImmersion ι) (g : X ⟶ Y) (h : Y ⟶ Z) (hg : Smooth g) (hh : LocallyOfFinitePresentation h)
    (fac : ι ≫ f = g ≫ h) (x : X) (hx : g.base x ∈ h.smoothLocus) :
    ι.base x ∈ f.smoothLocus :=
  Scheme.Hom.mem_smoothLocus_of_fac f ι g h fac x hx

end AlgebraicGeometry
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"
end W6dGeneric
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"

namespace V3Glue
p2m_export "V3Glue" "Site.XO Site.Node ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "xU vertex eq_liftY_of_g_eq edgePt' Y q a j toGlueInput hq g toB_eq interior_setOf_q_eq πX Res X0 U σ mk S B ρ x thick f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

private theorem _root_.V3Glue.ChartInput.ιY_toDR_πX (n : N) :
    C.toGlueInput.ιY n ≫ C.toGlueInput.toDR ≫ C.πX = C.g n ≫ (C.ρ n ≫ C.σ n) := by
  rw [← Category.assoc, C.toGlueInput.ιY_toDR, Category.assoc]
  change C.q n ≫ (C.U n).ι ≫ C.πX = _
  rw [← C.toB_eq]
  rfl

p2m_export "V3Glue.ChartInput" "ιY_toDR_πX"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"

namespace V3Glue
p2m_export "V3Glue" "Site.XO Site.Node ChartInput"
namespace ChartInput
p2m_export "V3Glue.ChartInput" "xU vertex eq_liftY_of_g_eq edgePt' Y q a j toGlueInput hq g toB_eq interior_setOf_q_eq πX Res X0 U σ mk S B ρ x thick f mem_X0"
p2m_open "V3Glue.ChartInput V3Glue"

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

private theorem _root_.V3Glue.ChartInput.ιY_eq_edgePt'_of_g_eq_oRes (n : N) (d : Fin (C.thick n)) (y : C.Y n) (hy : C.g n y = oRes n d) :
    C.toGlueInput.ιY n y = C.edgePt' hRF oRes hoRes n d := by
  rw [C.eq_liftY_of_g_eq n (hRF n) (oRes n d) (hoRes n d) y hy]; rfl

p2m_export "V3Glue.ChartInput" "ιY_eq_edgePt'_of_g_eq_oRes"

private theorem _root_.V3Glue.ChartInput.exists_edgePt'_eq_of_g_eq_oRes (n : N) (y : C.Y n) (hy : C.g n y ∈ Set.range (oRes n)) :
    ∃ d : Fin (C.thick n), C.toGlueInput.ιY n y = C.edgePt' hRF oRes hoRes n d := by
  obtain ⟨d, hd⟩ := hy
  exact ⟨d, C.ιY_eq_edgePt'_of_g_eq_oRes hRF oRes hoRes n d y hd.symm⟩

p2m_export "V3Glue.ChartInput" "exists_edgePt'_eq_of_g_eq_oRes"

private theorem _root_.V3Glue.ChartInput.g_not_mem_range_oRes_of_ne_edgePt' (n : N) (y : C.Y n)
    (hne : ∀ d : Fin (C.thick n), C.toGlueInput.ιY n y ≠ C.edgePt' hRF oRes hoRes n d) :
    C.g n y ∉ Set.range (oRes n) := fun h => by
  obtain ⟨d, hd⟩ := C.exists_edgePt'_eq_of_g_eq_oRes hRF oRes hoRes n y h
  exact hne d hd

p2m_export "V3Glue.ChartInput" "g_not_mem_range_oRes_of_ne_edgePt'"
end V3Glue.ChartInput
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"

namespace MvPolynomial
p2m_export "MvPolynomial" "X map coeff R aeval_X ext support aeval_def algebraMap_apply comap algebraMap_eq C monomial coeff_zero sum_def notMem_support_iff aeval_C induction_on aeval CrossingQuotient.Resolution CrossingQuotient.Resolution.exists_ι_apply_eq CrossingQuotient.Resolution.toCrossing CrossingQuotient.Resolution.toSpec CrossingQuotient.U CrossingQuotient.V CrossingQuotient CrossingQuotient.Resolution.isProper_toCrossing"
namespace CrossingQuotient
p2m_export "MvPolynomial.CrossingQuotient" "chartScheme Resolution Resolution.exists_ι_apply_eq Resolution.toCrossing Resolution.toSpec U V U_mul_V lift mk mk_surjective monomial monomial_natCast monomial_neg_natCast originIdeal linearIndependent_monomial_and_span_eq_top Resolution.isProper_toCrossing"
namespace Resolution
p2m_export "MvPolynomial.CrossingQuotient.Resolution" "ι exists_ι_apply_eq toCrossing toSpec ι_toSpec origin eq_origin_pt_of_mem isProper_toCrossing"
p2m_open "MvPolynomial.CrossingQuotient.Resolution MvPolynomial.CrossingQuotient MvPolynomial"

variable {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) (ht : t ∈ 𝔭)

theorem ι_apply_eq_origin_of_U_mem_of_V_mem [𝔭.IsMaximal] (h𝔭t : 𝔭 ≤ Ideal.span {t}) (i : Fin e)
    (P : chartScheme t) (hU : U t ∈ P.asIdeal) (hV : V t ∈ P.asIdeal) :
    ι t e i P = origin t e 𝔭 ht i := by
  have htP : algebraMap W (CrossingQuotient W t) t ∈ P.asIdeal := by
    rw [← U_mul_V]; exact P.asIdeal.mul_mem_left _ hV
  have h : P = ⟨originIdeal t 𝔭 ht, inferInstance⟩ :=
    eq_origin_pt_of_mem t 𝔭 ht hU hV (fun w hw => by
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp (h𝔭t hw)
      rw [map_mul]
      exact P.asIdeal.mul_mem_left _ htP)
  subst h
  rfl

theorem ι_apply_mem_range_origin_of_U_mem_of_V_mem [𝔭.IsMaximal] (h𝔭t : 𝔭 ≤ Ideal.span {t}) (i : Fin e)
    (P : chartScheme t) (hU : U t ∈ P.asIdeal) (hV : V t ∈ P.asIdeal) :
    ι t e i P ∈ Set.range (origin t e 𝔭 ht) :=
  ⟨i, (ι_apply_eq_origin_of_U_mem_of_V_mem t e 𝔭 ht h𝔭t i P hU hV).symm⟩

end MvPolynomial.CrossingQuotient.Resolution
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry"

namespace V3Asm
p2m_export "V3Asm" "πX SiteHyps R C D Y toDR toBase hq mem_X0_iff width hRF p_mem_maximalIdeal ξ oRes hoRes comp edgePt"
p2m_open "V3Asm"

p2m_open "ModularCurve MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient TopologicalSpace"

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (H : SiteHyps p 𝔛 O κ toκ)

include 𝔛 in
theorem isProper_πX' : IsProper (πX p O) := by
  haveI := 𝔛.isProper
  exact MorphismProperty.pullback_snd _ _ inferInstance

include 𝔛 in
theorem flat_πX' : Flat (πX p O) := by
  haveI := 𝔛.flat
  exact MorphismProperty.pullback_snd _ _ inferInstance

include hϖ in
theorem p_ne_zero' : ((p : ℕ) : O) ≠ 0 := by
  intro h
  apply IsDiscreteValuationRing.not_a_field O
  rw [hϖ, h, Ideal.span_singleton_eq_bot.mpr rfl]

theorem etale_f' (n : V3Glue.Site.Node p 𝔛 κ) : Etale ((C p 𝔛 O κ toκ hϖ H).f n) := by
  haveI := H.nodeFinite
  exact (R p 𝔛 O κ toκ hϖ H).etale_toChartInput_f _ n

theorem toDR_proper' : IsProper (toDR p 𝔛 O κ toκ hϖ H) :=
  (D p 𝔛 O κ toκ hϖ H).isProper_toDR (hq p 𝔛 O κ toκ hϖ H) (fun n => show IsProper ((C p 𝔛 O κ toκ hϖ H).q n) from inferInstance)

theorem isProper' : IsProper (toBase p 𝔛 O κ toκ hϖ H) := by
  haveI := toDR_proper' p 𝔛 O κ toκ hϖ H
  haveI := isProper_πX' p 𝔛 O
  show IsProper (toDR p 𝔛 O κ toκ hϖ H ≫ πX p O)
  infer_instance

include hϖ in
theorem isIntegral_XO' : IsIntegral (V3Glue.Site.XO p O) :=
  ModularCurve.DRModel.isIntegral_pullback_toBase p O hϖ

theorem snd_preimage_basicOpen_le_X0' :
    pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) ≤
      (D p 𝔛 O κ toκ hϖ H).X0 := by
  intro x hx
  refine (mem_X0_iff p 𝔛 O κ toκ hϖ H x).mpr fun n hn => ?_
  subst hn
  exact DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p O κ toκ _ hx

theorem nonempty_X0' : Nonempty ((D p 𝔛 O κ toκ hϖ H).X0) := by
  haveI := isIntegral_XO' p O hϖ
  haveI := flat_πX' p 𝔛 O
  obtain ⟨x⟩ := (inferInstance : Nonempty ↥(V3Glue.Site.XO p O))
  let ξ : ↥(Spec (CommRingCat.of O)) := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ : ξ ⤳ (πX p O).base x := (PrimeSpectrum.le_iff_specializes ξ ((πX p O).base x)).mp bot_le
  obtain ⟨x', -, hx'⟩ := Flat.generalizingMap (πX p O) hξ
  refine ⟨⟨x', snd_preimage_basicOpen_le_X0' p 𝔛 O κ toκ hϖ H ?_⟩⟩
  show (πX p O).base x' ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O)
  rw [show (πX p O).base x' = ξ from hx']
  show ((p : ℕ) : O) ∉ (⊥ : Ideal O)
  rw [Ideal.mem_bot]
  exact p_ne_zero' p O hϖ

theorem irreducibleSpace_Y : IrreducibleSpace (Y p 𝔛 O κ toκ hϖ H) := by
  haveI := isIntegral_XO' p O hϖ
  haveI := nonempty_X0' p 𝔛 O κ toκ hϖ H
  haveI := H.nodeFinite
  haveI : Fintype (V3Glue.Site.Node p 𝔛 κ) := Fintype.ofFinite _
  exact (D p 𝔛 O κ toκ hϖ H).irreducibleSpace_glued (hq p 𝔛 O κ toκ hϖ H) (fun n => H.hxcl n)
    (fun n => (D p 𝔛 O κ toκ hϖ H).interior_preimage_toDR_x_eq_empty (hq p 𝔛 O κ toκ hϖ H) n ((C p 𝔛 O κ toκ hϖ H).interior_setOf_q_eq n))

theorem fst_preimage_smoothLocus_le_X0' :
    pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus ≤ (D p 𝔛 O κ toκ hϖ H).X0 := by
  intro x hx
  refine (mem_X0_iff p 𝔛 O κ toκ hϖ H x).mpr fun n hn => ?_
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

theorem toDR_iso_smoothLocus' :
    IsIso (toDR p 𝔛 O κ toκ hϖ H ∣_ (pullback.fst (DRModel.toBase p) _ ⁻¹ᵁ 𝔛.smoothLocus)) :=
  (D p 𝔛 O κ toκ hϖ H).isIso_toDR_restrict (hq p 𝔛 O κ toκ hϖ H) (fst_preimage_smoothLocus_le_X0' p 𝔛 O κ toκ hϖ H)

local notation "𝕐" => Y p 𝔛 O κ toκ hϖ H
local notation "𝕎" => width p 𝔛 O κ toκ hϖ H

scoped instance toBase_lfp : LocallyOfFinitePresentation (toBase p 𝔛 O κ toκ hϖ H) := by
  haveI := isProper' p 𝔛 O κ toκ hϖ H
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_isNoetherianRing (toBase p 𝔛 O κ toκ hϖ H)

def smoothOffEdges : (𝕐).Opens := (toBase p 𝔛 O κ toκ hϖ H).smoothLocus

def Vsm : (𝕐).Opens :=
  toDR p 𝔛 O κ toκ hϖ H ⁻¹ᵁ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus)

theorem smoothOfRelativeDimension_one_Vsm : SmoothOfRelativeDimension 1 ((Vsm p 𝔛 O κ toκ hϖ H).ι ≫ toBase p 𝔛 O κ toκ hϖ H) := by

  let c := DRModel.toBase p
  let s := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
  let W : (V3Glue.Site.XO p O).Opens := pullback.fst c s ⁻¹ᵁ 𝔛.smoothLocus
  haveI := 𝔛.smoothLocus_relDim
  have hW : SmoothOfRelativeDimension 1 (W.ι ≫ πX p O) := by
    have hsq : IsPullback ((pullback.fst c s) ∣_ 𝔛.smoothLocus) W.ι 𝔛.smoothLocus.ι (pullback.fst c s) :=
      isPullback_morphismRestrict _ _
    have hbig : IsPullback ((pullback.fst c s) ∣_ 𝔛.smoothLocus) (W.ι ≫ πX p O) (𝔛.smoothLocus.ι ≫ c) s :=
      hsq.paste_vert (IsPullback.of_hasPullback c s)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hbig inferInstance

  haveI : IsIso (toDR p 𝔛 O κ toκ hϖ H ∣_ W) := toDR_iso_smoothLocus' p 𝔛 O κ toκ hϖ H
  have hfac : (Vsm p 𝔛 O κ toκ hϖ H).ι ≫ toBase p 𝔛 O κ toκ hϖ H = (toDR p 𝔛 O κ toκ hϖ H ∣_ W) ≫ (W.ι ≫ πX p O) := by
    change (toDR p 𝔛 O κ toκ hϖ H ⁻¹ᵁ W).ι ≫ toDR p 𝔛 O κ toκ hϖ H ≫ πX p O = _
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  rw [hfac]
  have : SmoothOfRelativeDimension (0 + 1) ((toDR p 𝔛 O κ toκ hϖ H ∣_ W) ≫ (W.ι ≫ πX p O)) :=
    smoothOfRelativeDimension_comp 0 1 (f := toDR p 𝔛 O κ toκ hϖ H ∣_ W) (W.ι ≫ πX p O)
  first | simpa using this | exact this

theorem Vsm_nonempty : ((Vsm p 𝔛 O κ toκ hϖ H : (𝕐).Opens) : Set 𝕐).Nonempty := by
  classical
  let c := DRModel.toBase p
  let s := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
  let W : (V3Glue.Site.XO p O).Opens := pullback.fst c s ⁻¹ᵁ 𝔛.smoothLocus

  haveI : Nonempty (Spec (CommRingCat.of O)) := inferInstance
  let pt : Spec (CommRingCat.of O) ⟶ V3Glue.Site.XO p O :=
    pullback.lift (s ≫ 𝔛.εinf.1) (𝟙 _) (by rw [Category.assoc, 𝔛.εinf.2, Category.comp_id, Category.id_comp])
  have hpt : ∀ t, pt.base t ∈ W := by
    intro t
    show (pullback.fst c s).base (pt.base t) ∈ 𝔛.smoothLocus
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact 𝔛.εinf_mem_smoothLocus ⟨_, rfl⟩
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of O)))

  haveI : IsIso (toDR p 𝔛 O κ toκ hϖ H ∣_ W) := toDR_iso_smoothLocus' p 𝔛 O κ toκ hϖ H
  obtain ⟨y, hy⟩ := (toDR p 𝔛 O κ toκ hϖ H ∣_ W).surjective ⟨pt.base t, hpt t⟩
  exact ⟨y.1, y.2⟩

theorem smoothOffEdges_smooth : SmoothOfRelativeDimension 1 ((smoothOffEdges p 𝔛 O κ toκ hϖ H).ι ≫ toBase p 𝔛 O κ toκ hϖ H) := by
  haveI := irreducibleSpace_Y p 𝔛 O κ toκ hϖ H
  haveI := smoothOfRelativeDimension_one_Vsm p 𝔛 O κ toκ hϖ H
  exact AlgebraicGeometry.smoothOfRelativeDimension_smoothLocus_ι_comp (toBase p 𝔛 O κ toκ hϖ H) 1
    (Vsm p 𝔛 O κ toκ hϖ H) (Vsm_nonempty p 𝔛 O κ toκ hϖ H)

theorem baseChangeMap_fst :
    DRModel.baseChangeMap toκ ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) := by
  delta DRModel.baseChangeMap
  rw [pullback.lift_fst, Category.comp_id]

include hϖ in

theorem exists_baseChangeMap_eq (x : ↥(V3Glue.Site.XO p O))
    (hx : x ∉ (πX p O) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    ∃ y, (DRModel.baseChangeMap toκ).base y = x := by
  classical
  let c := DRModel.toBase p
  let sO := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
  let sκ := Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))
  let t := Spec.map (CommRingCat.ofHom toκ)

  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top toκ)) ?_
    rw [hϖ, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

  have hxc : ((πX p O).base x).asIdeal = IsLocalRing.maximalIdeal O := by
    have hp : ((p : ℕ) : O) ∈ ((πX p O).base x).asIdeal := by
      by_contra h
      exact hx h
    have hle : IsLocalRing.maximalIdeal O ≤ ((πX p O).base x).asIdeal := by
      rw [hϖ, Ideal.span_le, Set.singleton_subset_iff]; exact hp
    exact (IsLocalRing.le_maximalIdeal ((πX p O).base x).isPrime.ne_top).antisymm hle |>.symm ▸ rfl
  have htc : (t.base (IsLocalRing.closedPoint κ)).asIdeal = IsLocalRing.maximalIdeal O := by
    change Ideal.comap toκ (IsLocalRing.closedPoint κ).asIdeal = _
    rw [show (IsLocalRing.closedPoint κ).asIdeal = ⊥ from Ideal.eq_bot_of_prime _, ← RingHom.ker_eq_comap_bot, hker]
  have hxt : (πX p O).base x = t.base (IsLocalRing.closedPoint κ) := PrimeSpectrum.ext (hxc.trans htc.symm)

  have hsq : IsPullback (DRModel.baseChangeMap toκ) (pullback.snd c sκ) (pullback.snd c sO) t := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback c sO)
    ·
      have ht : t ≫ sO = sκ := by
        rw [← Spec.map_comp]; congr 1; ext1; exact RingHom.ext_int _ _
      have hfst : DRModel.baseChangeMap toκ ≫ pullback.fst c sO = pullback.fst c sκ := baseChangeMap_fst p O κ toκ
      rw [hfst, ht]
      exact IsPullback.of_hasPullback c sκ
    ·
      delta DRModel.baseChangeMap
      rw [pullback.lift_snd]

  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd c sO) (g := t) x (IsLocalRing.closedPoint κ) hxt
  refine ⟨hsq.isoPullback.inv.base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hz1

include 𝔛 in

theorem mem_smoothLocus_πX_of_mem_basicOpen [LocallyOfFinitePresentation (πX p O)] (x : ↥(V3Glue.Site.XO p O))
    (hx : x ∈ (πX p O) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    x ∈ (πX p O).smoothLocus := by
  classical
  let c := DRModel.toBase p
  let sO := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
  let ℓ := Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))
  haveI : IsProper c := 𝔛.isProper
  haveI : LocallyOfFinitePresentation c := AlgebraicGeometry.locallyOfFinitePresentation_of_isNoetherianRing c

  have h1 : pullback.fst c sO ⁻¹ᵁ c.smoothLocus ≤ (πX p O).smoothLocus :=
    Scheme.Hom.preimage_smoothLocus_le_of_isPullback (IsPullback.of_hasPullback c sO)
  apply h1
  show (pullback.fst c sO).base x ∈ c.smoothLocus

  have hxD : c.base ((pullback.fst c sO).base x) ∈ PrimeSpectrum.basicOpen (p : ℤ) := by
    have hsq := congr($(pullback.condition (f := c) (g := sO)).base x)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hsq
    rw [hsq]
    change (p : ℤ) ∉ Ideal.comap (algebraMap ℤ O) ((πX p O).base x).asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hx

  haveI : Smooth (pullback.snd c ℓ) := 𝔛.smooth_away
  haveI : Flat ℓ := inferInstance
  have h2 : (pullback.snd c ℓ).smoothLocus ≤ pullback.fst c ℓ ⁻¹ᵁ c.smoothLocus :=
    Scheme.Hom.smoothLocus_le_preimage_of_isPullback (IsPullback.of_hasPullback c ℓ)
  have hrange : (pullback.fst c sO).base x ∈ Set.range (pullback.fst c ℓ).base := by
    rw [Scheme.Pullback.range_fst]
    show c.base _ ∈ Set.range ℓ.base
    erw [PrimeSpectrum.localization_away_comap_range (Localization.Away (p : ℤ)) (p : ℤ)]
    exact hxD
  obtain ⟨z, hz⟩ := hrange
  have hz' : z ∈ (pullback.snd c ℓ).smoothLocus := by rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  have := h2 hz'
  rw [← hz]
  exact this

theorem πX_mem_smoothLocus_of_mem_X0 [hπ : LocallyOfFinitePresentation (πX p O)] (x : ↥(V3Glue.Site.XO p O)) (hx : x ∈ (D p 𝔛 O κ toκ hϖ H).X0) :
    x ∈ (πX p O).smoothLocus := by
  classical
  by_cases hgen : x ∈ (πX p O) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)
  · exact mem_smoothLocus_πX_of_mem_basicOpen p 𝔛 O x hgen
  ·
    obtain ⟨y, rfl⟩ := exists_baseChangeMap_eq p O κ toκ hϖ x hgen
    have hnot : ¬ (y ∈ Set.range (𝔛.compInf κ).base ∧ y ∈ Set.range (𝔛.compZero κ).base) := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

      obtain ⟨n, hn1, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
      have hmem := ((D p 𝔛 O κ toκ hϖ H).mem_X0 _).mp hx n
      apply hmem
      show (DRModel.baseChangeMap toκ).base y =
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n
      rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.comp_app, hn1, ha]
    have hsm : y ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⁻¹ᵁ 𝔛.smoothLocus) :=
      (𝔛.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p κ y).mpr hnot

    let c := DRModel.toBase p
    let s := Spec.map (CommRingCat.ofHom (algebraMap ℤ O))
    let W : (V3Glue.Site.XO p O).Opens := pullback.fst c s ⁻¹ᵁ 𝔛.smoothLocus
    have hW : (DRModel.baseChangeMap toκ).base y ∈ W := by
      show (pullback.fst c s).base ((DRModel.baseChangeMap toκ).base y) ∈ 𝔛.smoothLocus
      rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, baseChangeMap_fst p O κ toκ]
      exact hsm
    haveI := 𝔛.smoothLocus_relDim
    have hWsm : Smooth (W.ι ≫ πX p O) := by
      have hsq : IsPullback ((pullback.fst c s) ∣_ 𝔛.smoothLocus) W.ι 𝔛.smoothLocus.ι (pullback.fst c s) :=
        isPullback_morphismRestrict _ _
      have hbig : IsPullback ((pullback.fst c s) ∣_ 𝔛.smoothLocus) (W.ι ≫ πX p O) (𝔛.smoothLocus.ι ≫ c) s :=
        hsq.paste_vert (IsPullback.of_hasPullback c s)
      haveI : Smooth (𝔛.smoothLocus.ι ≫ c) := SmoothOfRelativeDimension.smooth (n := 1) (f := 𝔛.smoothLocus.ι ≫ c)
      exact smooth_isStableUnderBaseChange.of_isPullback hbig inferInstance
    exact Scheme.Hom.mem_smoothLocus_of_mem_of_smooth (πX p O) W hWsm _ hW

include 𝔛 in
theorem πX_lfp : LocallyOfFinitePresentation (πX p O) := by
  haveI := isProper_πX' p 𝔛 O
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_isNoetherianRing (πX p O)

theorem mem_smoothOffEdges_X0 (x0 : (D p 𝔛 O κ toκ hϖ H).X0) :
    ((D p 𝔛 O κ toκ hϖ H).ιX0).base x0 ∈ smoothOffEdges p 𝔛 O κ toκ hϖ H := by
  have fac : (D p 𝔛 O κ toκ hϖ H).ιX0 ≫ toBase p 𝔛 O κ toκ hϖ H = (D p 𝔛 O κ toκ hϖ H).X0.ι ≫ πX p O := by
    change (D p 𝔛 O κ toκ hϖ H).ιX0 ≫ toDR p 𝔛 O κ toκ hϖ H ≫ πX p O = _
    rw [← Category.assoc]
    erw [(D p 𝔛 O κ toκ hϖ H).ιX0_toDR]
  have hι : IsOpenImmersion ((D p 𝔛 O κ toκ hϖ H).ιX0) := by
    show IsOpenImmersion ((C p 𝔛 O κ toκ hϖ H).toGlueInput.ιX0)
    infer_instance
  have hgsm : Smooth ((D p 𝔛 O κ toκ hϖ H).X0.ι) := inferInstance
  haveI hπlfp : LocallyOfFinitePresentation (πX p O) := πX_lfp p 𝔛 O
  exact Scheme.Hom.mem_smoothLocus_of_fac' (toBase p 𝔛 O κ toκ hϖ H) inferInstance ((D p 𝔛 O κ toκ hϖ H).ιX0) hι
    ((D p 𝔛 O κ toκ hϖ H).X0.ι) (πX p O) hgsm hπlfp fac x0
    (πX_mem_smoothLocus_of_mem_X0 p 𝔛 O κ toκ hϖ H (hπ := hπlfp) x0.1 x0.2)

theorem g_mem_smoothLocus_of_ne_edgePt (n : V3Glue.Site.Node p 𝔛 κ) (yn : (D p 𝔛 O κ toκ hϖ H).Y n)
    [LocallyOfFinitePresentation ((C p 𝔛 O κ toκ hϖ H).ρ n ≫ (C p 𝔛 O κ toκ hϖ H).σ n)]
    (hy : ∀ (m : V3Glue.Site.Node p 𝔛 κ) (d : Fin (𝕎 m)), ((D p 𝔛 O κ toκ hϖ H).ιY n).base yn ≠ edgePt p 𝔛 O κ toκ hϖ H m d) :
    ((C p 𝔛 O κ toκ hϖ H).g n).base yn ∈ ((C p 𝔛 O κ toκ hϖ H).ρ n ≫ (C p 𝔛 O κ toκ hϖ H).σ n).smoothLocus := by

  have hσ : (C p 𝔛 O κ toκ hϖ H).ρ n ≫ (C p 𝔛 O κ toκ hϖ H).σ n =
      MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n) := by
    rfl

  have hoff : ∀ z, z ∈ MvPolynomial.CrossingQuotient.Resolution.offOrigins ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n) →
      z ∈ ((C p 𝔛 O κ toκ hϖ H).ρ n ≫ (C p 𝔛 O κ toκ hϖ H).σ n).smoothLocus := by
    intro z hz
    have key : ∀ (k : (C p 𝔛 O κ toκ hϖ H).Res n ⟶ (C p 𝔛 O κ toκ hϖ H).B) (hk_lfp : LocallyOfFinitePresentation k),
        k = MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n) → z ∈ @Scheme.Hom.smoothLocus _ _ k hk_lfp := by
      intro k hk_lfp hk
      subst hk
      have hsm : SmoothOfRelativeDimension 1 ((MvPolynomial.CrossingQuotient.Resolution.offOrigins ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)).ι ≫
          MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)) :=
        MvPolynomial.CrossingQuotient.Resolution.smoothOfRelativeDimension_one_offOrigins ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)
      haveI := hsm
      haveI : Smooth ((MvPolynomial.CrossingQuotient.Resolution.offOrigins ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)).ι ≫
          MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)) :=
        SmoothOfRelativeDimension.smooth (n := 1)
          (f := (MvPolynomial.CrossingQuotient.Resolution.offOrigins ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)).ι ≫
            MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n))
      exact @Scheme.Hom.mem_smoothLocus_of_mem_of_smooth _ _ (MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n))
        hk_lfp (MvPolynomial.CrossingQuotient.Resolution.offOrigins ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)) this z hz
    exact key _ inferInstance hσ

  obtain ⟨i, z, hz⟩ := MvPolynomial.CrossingQuotient.Resolution.exists_ι_apply_eq ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n) (((C p 𝔛 O κ toκ hϖ H).g n).base yn)
  by_cases horig : MvPolynomial.CrossingQuotient.U ((p : ℕ) : O) ∈ z.asIdeal ∧ MvPolynomial.CrossingQuotient.V ((p : ℕ) : O) ∈ z.asIdeal
  ·
    exfalso
    have hmem : ((C p 𝔛 O κ toκ hϖ H).g n).base yn ∈ Set.range (oRes p 𝔛 O κ toκ hϖ H n) := by
      rw [← hz]
      exact MvPolynomial.CrossingQuotient.Resolution.ι_apply_mem_range_origin_of_U_mem_of_V_mem ((p : ℕ) : O)
        ((C p 𝔛 O κ toκ hϖ H).thick n) (IsLocalRing.maximalIdeal O) (p_mem_maximalIdeal p O hϖ) (hϖ ▸ le_rfl) i z horig.1 horig.2
    exact (C p 𝔛 O κ toκ hϖ H).g_not_mem_range_oRes_of_ne_edgePt' (hRF p 𝔛 O κ toκ hϖ H) (oRes p 𝔛 O κ toκ hϖ H) (hoRes p 𝔛 O κ toκ hϖ H) n yn
      (fun d => hy n d) hmem
  · rw [← hz]
    exact hoff _ (MvPolynomial.CrossingQuotient.Resolution.ι_apply_mem_offOrigins_of_not ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n) horig)

scoped instance ρσ_lfp (n : V3Glue.Site.Node p 𝔛 κ) : LocallyOfFinitePresentation ((C p 𝔛 O κ toκ hϖ H).ρ n ≫ (C p 𝔛 O κ toκ hϖ H).σ n) := by

  change LocallyOfFinitePresentation (MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n))
  haveI : IsProper (MvPolynomial.CrossingQuotient.Resolution.toCrossing ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)) :=
    MvPolynomial.CrossingQuotient.Resolution.isProper_toCrossing ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap O (MvPolynomial.CrossingQuotient O (((p : ℕ) : O) ^ (C p 𝔛 O κ toκ hϖ H).thick n))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  haveI : LocallyOfFiniteType (MvPolynomial.CrossingQuotient.Resolution.toSpec ((p : ℕ) : O) ((C p 𝔛 O κ toκ hϖ H).thick n)) := by
    delta MvPolynomial.CrossingQuotient.Resolution.toSpec
    infer_instance
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_isNoetherianRing _

theorem mem_smoothOffEdges :
    ∀ y : 𝕐, (∀ (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin (𝕎 n)), y ≠ edgePt p 𝔛 O κ toκ hϖ H n d) →
    y ∈ smoothOffEdges p 𝔛 O κ toκ hϖ H := by
  intro y hy
  rcases (D p 𝔛 O κ toκ hϖ H).ι_jointly_surjective y with ⟨x0, rfl⟩ | ⟨n, yn, rfl⟩
  · exact mem_smoothOffEdges_X0 p 𝔛 O κ toκ hϖ H x0
  · have hgsm : Smooth ((C p 𝔛 O κ toκ hϖ H).g n) := by

      haveI := etale_f' p 𝔛 O κ toκ hϖ H n
      haveI : Smooth ((C p 𝔛 O κ toκ hϖ H).f n) := inferInstance
      exact MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
    have fac : (D p 𝔛 O κ toκ hϖ H).ιY n ≫ toBase p 𝔛 O κ toκ hϖ H =
        (C p 𝔛 O κ toκ hϖ H).g n ≫ ((C p 𝔛 O κ toκ hϖ H).ρ n ≫ (C p 𝔛 O κ toκ hϖ H).σ n) :=
      (C p 𝔛 O κ toκ hϖ H).ιY_toDR_πX n
    haveI hρσ : LocallyOfFinitePresentation ((C p 𝔛 O κ toκ hϖ H).ρ n ≫ (C p 𝔛 O κ toκ hϖ H).σ n) := ρσ_lfp p 𝔛 O κ toκ hϖ H n
    have hι : IsOpenImmersion ((D p 𝔛 O κ toκ hϖ H).ιY n) := by
      show IsOpenImmersion ((C p 𝔛 O κ toκ hϖ H).toGlueInput.ιY n)
      infer_instance
    exact Scheme.Hom.mem_smoothLocus_of_fac' (toBase p 𝔛 O κ toκ hϖ H) inferInstance ((D p 𝔛 O κ toκ hϖ H).ιY n) hι
      ((C p 𝔛 O κ toκ hϖ H).g n) ((C p 𝔛 O κ toκ hϖ H).ρ n ≫ (C p 𝔛 O κ toκ hϖ H).σ n) hgsm (ρσ_lfp p 𝔛 O κ toκ hϖ H n) fac yn
      (g_mem_smoothLocus_of_ne_edgePt p 𝔛 O κ toκ hϖ H n yn hy)

end V3Asm
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry P2MW.S_V3Asm_exists_smoothOffEdges.V3Asm"

end
p2m_reactivate "P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient.Resolution P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial P2MW.S_V3Asm_exists_smoothOffEdges.MvPolynomial.CrossingQuotient P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry.Scheme.Hom P2MW.S_V3Asm_exists_smoothOffEdges.AlgebraicGeometry P2MW.S_V3Asm_exists_smoothOffEdges.V3Asm"

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : ModularCurve.DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (H : V3Asm.SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) :
    ∃ Wo : (V3Asm.Y p 𝔛 O κ toκ hϖ H).Opens, SmoothOfRelativeDimension 1 (Wo.ι ≫ (V3Asm.toBase p 𝔛 O κ toκ hϖ H)) ∧
      ∀ y : (V3Asm.Y p 𝔛 O κ toκ hϖ H), (∀ (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n)), y ≠ V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d) → y ∈ Wo :=
  ⟨V3Asm.smoothOffEdges p 𝔛 O κ toκ hϖ H, V3Asm.smoothOffEdges_smooth p 𝔛 O κ toκ hϖ H, V3Asm.mem_smoothOffEdges p 𝔛 O κ toκ hϖ H⟩

end S_V3Asm_exists_smoothOffEdges
end P2MW
export P2MW.S_V3Asm_exists_smoothOffEdges (solution)
