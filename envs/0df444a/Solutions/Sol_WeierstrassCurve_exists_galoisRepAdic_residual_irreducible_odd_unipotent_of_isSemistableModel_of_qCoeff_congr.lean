-- Prove2me | solution 1 for WeierstrassCurve.exists_galoisRepAdic_residual_irreducible_odd_unipotent_of_isSemistableModel_of_qCoeff_congr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b6d1e554-4206-5b31-89a1-e176dde97079

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_ResidualEquiv
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_galoisRepAdic_charpoly_frobenius_eq_of_ringHom_integralClosure
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_GaloisRepAdic_charpoly_residual
import Theorems.Thm_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_charpoly_baseChangeAlong
import Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_isUnipotentOnInertiaAt
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Theorems.Thm_WeierstrassCurve_IsIntegralModelOf_galoisTrace_det_frobenius
import Theorems.Thm_WeierstrassCurve_IsIntegralModelOf_modRepIsIrreducible_iff
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isOdd
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_galoisRepAdic_residual_irreducible_odd_unipotent_of_isSemistableModel_of_qCoeff_congr
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D"
p2m_attr_erase "simp" "ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.mem_fibSet"

set_option autoImplicit false
open scoped WeierstrassCurve.Affine
open Polynomial

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Ws25
namespace Attach

theorem charpoly_eq_of_finrank_eq_two {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (h : Module.finrank k V = 2) (f : V →ₗ[k] V) :
    f.charpoly = X ^ 2 - C (LinearMap.trace k V f) * X + C (LinearMap.det f) := by
  classical
  let b := Module.finBasisOfFinrankEq k V h
  rw [← f.charpoly_toMatrix b, Matrix.charpoly_fin_two, ← LinearMap.trace_eq_matrix_trace k b f,
    LinearMap.det_toMatrix b f]

theorem isLocalHom_of_field {k k' : Type*} [Field k] [Field k'] (φ : k →+* k') : IsLocalHom φ := by
  refine ⟨fun a ha => ?_⟩
  rcases eq_or_ne a 0 with rfl | h
  · rw [map_zero] at ha
    exact absurd ha not_isUnit_zero
  · exact IsUnit.mk0 a h

theorem map_quadratic {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R) :
    (X ^ 2 - C a * X + C b).map φ = X ^ 2 - C (φ a) * X + C (φ b) := by
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C]

theorem det_eq_of_charpoly_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (h : Module.finrank k V = 2) (f : V →ₗ[k] V) {a b : k} (hc : f.charpoly = X ^ 2 - C a * X + C b) :
    LinearMap.det f = b := by
  have h1 := charpoly_eq_of_finrank_eq_two h f
  rw [hc] at h1
  have := congrArg (fun q : k[X] => q.coeff 0) h1
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_zero, mul_zero, sub_zero, coeff_C_zero] at this
  simpa using this.symm

section Residual

theorem charpoly_residualGaloisRepOf (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hgood : W.IsGoodPrimeFor ℓ)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B.LiesOverPrime ℓ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : B.IsFrobeniusAt τ ℓ) :
    LinearMap.charpoly (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).ρ τ) =
      X ^ 2 - C (((W.apOfModel ℓ : ℤ) : ZMod p)) * X + C ((ℓ : ZMod p)) := by
  set r := (W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker with hr
  have hmodel : W.IsIntegralModelOf (W.map (Int.castRingHom ℚ)) := ⟨1, one_smul _ _⟩
  obtain ⟨htr, hdet⟩ := hmodel.galoisTrace_det_frobenius p ℓ Fact.out hℓ hℓp hgood B hB τ hτ
  have h2 : Module.finrank (ZMod p) r.V = 2 := r.finrank_eq
  have hc := charpoly_eq_of_finrank_eq_two h2 (r.ρ τ)
  have htr' : LinearMap.trace (ZMod p) r.V (r.ρ τ) = ((W.apOfModel ℓ : ℤ) : ZMod p) := htr
  have hdet' : LinearMap.det (r.ρ τ) = (ℓ : ZMod p) := hdet
  rw [htr', hdet'] at hc
  exact hc

theorem isUnipotentOnInertiaAt_of_charpoly_frobenius {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (ρ₂ : GaloisRepAdic k) (T : Finset ℕ)
    (hρ₂ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ T → W.IsGoodPrimeFor ℓ → ℓ ≠ p →
      ∀ (B : ValuationSubring (AlgebraicClosure ℚ)) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
          LinearMap.charpoly (ρ₂.ρ τ) = X ^ 2 - C (((W.apOfModel ℓ : ℤ) : k)) * X + C ((ℓ : k))) :
    ρ₂.IsUnipotentOnInertiaAt q := by
  classical
  have hp : p.Prime := Fact.out
  haveI hell : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (RingHom.injective_int _)).mpr hΔ)⟩
  have hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed_light (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ))
      (by exact_mod_cast hp.ne_zero)
  have hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p) :=
    WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel (W.map (Int.castRingHom ℚ)) p
  set ρW : GaloisRepAdic (ZMod p) := GaloisRepAdic.ofResidualGaloisRep
    ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker) with hρW
  have hWunip : ρW.IsUnipotentOnInertiaAt q :=
    WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_isUnipotentOnInertiaAt W p hΔ hW hcard hker hq hqp
  set φ : ZMod p →+* k := ZMod.castHom (dvd_refl p) k with hφdef
  have hφ : IsLocalHom φ := isLocalHom_of_field φ
  set T' : Finset ℕ := insert p (T ∪ (W.Δ.natAbs).primeFactors) with hT'
  have hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ T' → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        LinearMap.charpoly ((ρW.baseChangeAlong φ hφ).ρ τ) = LinearMap.charpoly (ρ₂.ρ τ) := by
    intro ℓ hℓ hℓT' B τ hB hτ
    have hℓp : ℓ ≠ p := fun h => hℓT' (h ▸ Finset.mem_insert_self _ _)
    have hℓT : ℓ ∉ T := fun h => hℓT' (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hgood : W.IsGoodPrimeFor ℓ := by
      intro h
      exact hℓT' (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hℓ, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hΔ⟩)))
    rw [GaloisRepAdic.charpoly_baseChangeAlong φ hφ ρW τ, hρW,
      show LinearMap.charpoly ((GaloisRepAdic.ofResidualGaloisRep
        ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker)).ρ τ) =
          LinearMap.charpoly (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).ρ τ) from rfl,
      charpoly_residualGaloisRepOf W p hcard hker hℓ hℓp hgood B hB τ hτ, map_quadratic, map_intCast, map_natCast,
      hρ₂ ℓ hℓ hℓT hgood hℓp B τ hB hτ]
  intro P hP σ hσ
  rw [← GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq (ρW.baseChangeAlong φ hφ) ρ₂ T' hfrob σ]
  exact GaloisRepAdic.isUnipotentOnInertiaAt_baseChangeAlong φ hφ ρW hWunip P hP σ hσ

end Residual

open scoped TensorProduct in

private theorem _root_.ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible' {k : Type} [Field k] {ρ : ResidualGaloisRep k}
    (h : ρ.IsAbsolutelyIrreducible) : ρ.IsIrreducible := by
  classical
  intro W hW
  set K := AlgebraicClosure k

  have hstab : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ W.baseChange K, (ρ.baseChange K).ρ σ x ∈ W.baseChange K := by
    intro σ x hx

    let f : W →ₗ[k] W := (ρ.ρ σ).restrict (fun w hw => hW σ w hw)
    have hf : (ρ.ρ σ) ∘ₗ W.subtype = W.subtype ∘ₗ f := by ext w; rfl
    obtain ⟨y, rfl⟩ := hx
    show ((ρ.ρ σ).baseChange K) ((W.subtype.baseChange K) y) ∈ W.baseChange K
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hf, LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact ⟨_, rfl⟩
  rcases h (W.baseChange K) hstab with hbot | htop
  ·
    left
    have h0 : Module.finrank K (W.baseChange K) = 0 := by rw [hbot, finrank_bot]
    have hW0 : Module.finrank k W = 0 := by
      rw [← Module.finrank_baseChange (R := K), ← h0]
      exact (Submodule.toBaseChange.toLinearEquiv K W).finrank_eq
    exact Submodule.finrank_eq_zero.mp hW0
  ·
    right
    have h2 : Module.finrank K (W.baseChange K) = 2 := by
      rw [htop, finrank_top]
      show Module.finrank K (K ⊗[k] ρ.V) = 2
      rw [Module.finrank_baseChange, ρ.finrank_eq]
    have hW2 : Module.finrank k W = 2 := by
      rw [← Module.finrank_baseChange (R := K), ← h2]
      exact (Submodule.toBaseChange.toLinearEquiv K W).finrank_eq
    apply Submodule.eq_top_of_finrank_eq
    rw [hW2, ρ.finrank_eq]

p2m_alias "P2MW.S_WeierstrassCurve_exists_galoisRepAdic_residual_irreducible_odd_unipotent_of_isSemistableModel_of_qCoeff_congr.ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible'" "ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible'"

theorem exists_rangeIncl_adjoin_qCoeff {L : ℕ} [NeZero L] {k : ℤ} (S : Set ℕ) (hLS : ∀ q : ℕ, q.Prime → q ∣ L → q ∈ S)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) k)
    (chig : CuspForm.heckeAlgebra L k S →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L) (hℓS : ℓ ∉ S),
      chig (CuspForm.heckeAlgebra.T hℓ hℓL hℓS) = ModularFormClass.qCoeff g ℓ) :
    ∃ incl : chig.range →+* Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n),
      ∀ x : chig.range, ((incl x : Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)) : ℂ) = (x : ℂ) := by
  classical
  set A := Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n) with hA

  have hval : ∀ t : CuspForm.heckeAlgebra L k S, chig t ∈ A := by
    rintro ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨ℓ, hℓ, hℓL, hℓS, rfl⟩ | ⟨q, hqL, hq, hqS, rfl⟩
      · rw [show (⟨CuspForm.heckeTLin k hℓ hℓL, _⟩ : CuspForm.heckeAlgebra L k S) = CuspForm.heckeAlgebra.T hℓ hℓL hℓS from rfl,
          hchig]
        exact Algebra.subset_adjoin ⟨ℓ, rfl⟩
      · exact absurd (hLS q hq hqL) hqS
    | algebraMap n =>
      rw [show (⟨algebraMap ℤ _ n, _⟩ : CuspForm.heckeAlgebra L k S) = algebraMap ℤ (CuspForm.heckeAlgebra L k S) n from rfl,
        eq_intCast, map_intCast chig]
      exact Subalgebra.intCast_mem A n
    | add a b ha hb iha ihb =>
      rw [show (⟨a + b, _⟩ : CuspForm.heckeAlgebra L k S) = ⟨a, ha⟩ + ⟨b, hb⟩ from rfl, chig.map_add]
      exact A.add_mem iha ihb
    | mul a b ha hb iha ihb =>
      rw [show (⟨a * b, _⟩ : CuspForm.heckeAlgebra L k S) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, chig.map_mul]
      exact A.mul_mem iha ihb
  have hrange : ∀ x : chig.range, (x : ℂ) ∈ A := by
    rintro ⟨x, t, rfl⟩; exact hval t
  exact ⟨(chig.range.subtype).codRestrict A (fun x => hrange x), fun x => rfl⟩

end Ws25.Attach

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Ws25.Attach in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) {M : ℕ} [NeZero M] {L : ℕ} [NeZero L]
    (hLM : L ∣ M)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNewform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
:
    ∃ (S : Finset ℕ)
    (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (_ : Finite (IsLocalRing.ResidueField O'))
      (_ : CharZero O') (_ : (p : O') ∈ IsLocalRing.maximalIdeal O')
      (chig : CuspForm.heckeAlgebra L 2 (↑S : Set ℕ) →+* ℂ)
      (iota : chig.range →+* O') (ρ : GaloisRepAdic O'),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ L) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ L) (hℓS : ℓ ∉ (↑S : Set ℕ)),
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X
                  + C ((ℓ : O'))) ∧
      ρ.residual.IsIrreducible ∧ ρ.residual.IsOdd ∧
      ∀ q : ℕ, q.Prime → q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsUnipotentOnInertiaAt q := by
  classical
  have hp : p.Prime := Fact.out
  have hL0 : L ≠ 0 := NeZero.ne L
  haveI hell : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨by rw [WeierstrassCurve.map_Δ]; exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (RingHom.injective_int _)).mpr hΔ)⟩
  have hmodel : W.IsIntegralModelOf (W.map (Int.castRingHom ℚ)) := ⟨1, one_smul _ _⟩

  set S : Finset ℕ := insert p L.primeFactors with hS
  have hpS : p ∈ S := Finset.mem_insert_self _ _
  have hLS : ∀ r : ℕ, r.Prime → r ∣ L → r ∈ S := fun r hr hrL =>
    Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hr, hrL, hL0⟩)

  obtain ⟨chig, -, hchig, -⟩ := hg.isNormalizedEigenform.exists_ringHom_heckeAlgebra (↑S : Set ℕ)
  obtain ⟨incl, hincl⟩ := exists_rangeIncl_adjoin_qCoeff (↑S : Set ℕ) (fun r hr hrL => by exact_mod_cast hLS r hr hrL)
    g chig hchig

  haveI : 𝔪.IsPrime := h𝔪.isPrime
  letI : Field (integralClosure ℤ ℂ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hpk : ((p : ℕ) : integralClosure ℤ ℂ ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔪
  haveI : CharP (integralClosure ℤ ℂ ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk
  obtain ⟨O, _, _, _, _, _, _, ι, ψ, ρ, hpO, hιinj, hkerψ, hcompat, hρ, -⟩ :=
    hg.isNormalizedEigenform.exists_galoisRepAdic_charpoly_frobenius_eq_of_ringHom_integralClosure hp
      (Ideal.Quotient.mk 𝔪 : integralClosure ℤ ℂ →+* integralClosure ℤ ℂ ⧸ 𝔪)
  set iota : chig.range →+* O := ι.comp incl with hiota
  have hiotaT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      (iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓL hℓS) =
        ι ⟨ModularFormClass.qCoeff g ℓ, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩ := by
    intro ℓ hℓ hℓL hℓS
    rw [hiota, RingHom.comp_apply, RingHom.comp_apply]
    congr 1
    apply Subtype.ext
    rw [hincl, RingHom.coe_rangeRestrict, hchig ℓ hℓ hℓL hℓS]

  set kO := IsLocalRing.ResidueField O with hkO
  have hpkO : ((p : ℕ) : kO) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O) p]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hpO
  haveI : CharP kO p := (CharP.charP_iff_prime_eq_zero hp).mpr hpkO

  have hres : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      IsLocalRing.residue O (ι ⟨ModularFormClass.qCoeff g ℓ, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩) =
        ((W.apOfModel ℓ : ℤ) : kO) := by
    intro ℓ hℓ hgood hℓM hℓp
    obtain ⟨a, ha, ha𝔪⟩ := hcong ℓ hℓ hgood hℓM hℓp
    have h1 : ψ (ι ⟨ModularFormClass.qCoeff g ℓ, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩) = Ideal.Quotient.mk 𝔪 a :=
      hcompat _ a ha
    have h2 : Ideal.Quotient.mk 𝔪 a = Ideal.Quotient.mk 𝔪 ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem a _).mpr ha𝔪
    have h3 : ι ⟨ModularFormClass.qCoeff g ℓ, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩ - ((W.apOfModel ℓ : ℤ) : O) ∈
        IsLocalRing.maximalIdeal O := by
      rw [← hkerψ, RingHom.mem_ker, map_sub, h1, h2, map_intCast, map_intCast, sub_self]
    rw [← sub_eq_zero, ← map_intCast (IsLocalRing.residue O), ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr h3

  have hρ₂ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S ∪ M.primeFactors → W.IsGoodPrimeFor ℓ → ℓ ≠ p →
      ∀ (B : ValuationSubring (AlgebraicClosure ℚ)) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
          LinearMap.charpoly ((GaloisRepAdic.ofResidualGaloisRep ρ.residual).ρ τ) =
            X ^ 2 - C (((W.apOfModel ℓ : ℤ) : kO)) * X + C ((ℓ : kO)) := by
    intro ℓ hℓ hℓT hgood hℓp B τ hB hτ
    have hℓS : ℓ ∉ S := fun h => hℓT (Finset.mem_union_left _ h)
    have hℓL : ¬ ℓ ∣ L := fun h => hℓS (hLS ℓ hℓ h)
    have hℓM : ¬ ℓ ∣ M := fun h => hℓT (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hℓ, h, NeZero.ne M⟩))
    rw [show LinearMap.charpoly ((GaloisRepAdic.ofResidualGaloisRep ρ.residual).ρ τ) =
        LinearMap.charpoly (ρ.residual.ρ τ) from rfl,
      GaloisRepAdic.charpoly_residual ρ τ, hρ ℓ hℓ hℓL hℓp B hB τ hτ, map_quadratic, hres ℓ hℓ hgood hℓM hℓp, map_natCast]

  have hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed_light (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ))
      (by exact_mod_cast hp.ne_zero)
  have hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p) :=
    WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel (W.map (Int.castRingHom ℚ)) p
  set rW := (W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker with hrW
  have hrWirr : rW.IsIrreducible :=
    (WeierstrassCurve.residualGaloisRepOf_isIrreducible_iff _ p hcard hker).mpr ((hmodel.modRepIsIrreducible_iff p).mp hirr)
  have hrWodd : rW.IsOdd := WeierstrassCurve.residualGaloisRepOf_isOdd _ p hcard hker
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hrWabs : rW.IsAbsolutelyIrreducible :=
    ResidualGaloisRep.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd rW h2p hrWirr hrWodd
  set φ : ZMod p →+* kO := ZMod.castHom (dvd_refl p) kO with hφdef
  letI : Algebra (ZMod p) kO := φ.toAlgebra
  set ρ₁ : ResidualGaloisRep kO := rW.baseChangeAlong φ with hρ₁
  have hρ₁abs : ρ₁.IsAbsolutelyIrreducible := hrWabs.baseChangeAlong φ
  have hρ₁c : ∀ σ, LinearMap.charpoly (ρ₁.ρ σ) = (LinearMap.charpoly (rW.ρ σ)).map φ := by
    intro σ
    show LinearMap.charpoly ((rW.ρ σ).baseChange kO) = _
    rw [LinearMap.charpoly_baseChange]
    rfl

  set T' : Finset ℕ := insert p ((S ∪ M.primeFactors) ∪ (W.Δ.natAbs).primeFactors) with hT'
  have hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ T' → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        LinearMap.charpoly ((GaloisRepAdic.ofResidualGaloisRep ρ₁).ρ τ) =
          LinearMap.charpoly ((GaloisRepAdic.ofResidualGaloisRep ρ.residual).ρ τ) := by
    intro ℓ hℓ hℓT' B τ hB hτ
    have hℓp : ℓ ≠ p := fun h => hℓT' (h ▸ Finset.mem_insert_self _ _)
    have hℓT : ℓ ∉ S ∪ M.primeFactors := fun h => hℓT' (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hgood : W.IsGoodPrimeFor ℓ := by
      intro h
      exact hℓT' (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hℓ, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hΔ⟩)))
    rw [show LinearMap.charpoly ((GaloisRepAdic.ofResidualGaloisRep ρ₁).ρ τ) = LinearMap.charpoly (ρ₁.ρ τ) from rfl,
      hρ₁c τ, hrW, charpoly_residualGaloisRepOf W p hcard hker hℓ hℓp hgood B hB τ hτ, map_quadratic, map_intCast,
      map_natCast, hρ₂ ℓ hℓ hℓT hgood hℓp B τ hB hτ]
  have hall : ∀ σ, (ρ₁.ρ σ).charpoly = (ρ.residual.ρ σ).charpoly := fun σ =>
    GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq (GaloisRepAdic.ofResidualGaloisRep ρ₁)
      (GaloisRepAdic.ofResidualGaloisRep ρ.residual) T' hfrob σ
  have habs : ρ.residual.IsAbsolutelyIrreducible :=
    ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq ρ₁ ρ.residual hρ₁abs hall
  have hirrρ : ρ.residual.IsIrreducible := habs.isIrreducible'

  have hoddρ : ρ.residual.IsOdd := by
    intro c hc hc1
    have hW1 : LinearMap.det (rW.ρ c) = -1 := hrWodd c hc hc1
    have h1 : LinearMap.det (ρ₁.ρ c) = -1 := by
      show LinearMap.det ((rW.ρ c).baseChange kO) = -1
      rw [LinearMap.det_baseChange, hW1, map_neg, map_one]
    have hq := charpoly_eq_of_finrank_eq_two ρ₁.finrank_eq (ρ₁.ρ c)
    rw [hall c] at hq
    have := det_eq_of_charpoly_eq ρ.residual.finrank_eq (ρ.residual.ρ c) hq
    rw [this, h1]

  have hunip : ∀ q : ℕ, q.Prime → q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsUnipotentOnInertiaAt q :=
    fun q hq hqp => isUnipotentOnInertiaAt_of_charpoly_frobenius p W hΔ hW hq hqp _ (S ∪ M.primeFactors) hρ₂

  refine ⟨S, O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hpO,
    chig, iota, ρ, hchig, ?_, hirrρ, hoddρ, hunip⟩
  intro ℓ hℓ hℓL hℓS A hA σ hσ
  have hℓp : ℓ ≠ p := fun h => hℓS (by rw [h]; exact_mod_cast hpS)
  rw [hρ ℓ hℓ hℓL hℓp A hA σ hσ, hiotaT ℓ hℓ hℓL hℓS]

end S_WeierstrassCurve_exists_galoisRepAdic_residual_irreducible_odd_unipotent_of_isSemistableModel_of_qCoeff_congr
end P2MW
export P2MW.S_WeierstrassCurve_exists_galoisRepAdic_residual_irreducible_odd_unipotent_of_isSemistableModel_of_qCoeff_congr (solution)
