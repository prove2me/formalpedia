-- Prove2me | solution 1 for WeierstrassCurve.exists_ideal_heckeAlgebra_weight_le_succ_pow_mul_of_pow_mul_of_exists_prime_dvd_mod_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c4a2c907-7973-5326-8f47-a62b2ffab3cb

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_hasIntegralStructure_of_two_le
import Theorems.Thm_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra
import Theorems.Thm_ModPForms_modPCusp_le_modPMod
import Theorems.Thm_ModPForms_exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure
import Theorems.Thm_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible
import Theorems.Thm_WeierstrassCurve_exists_ideal_heckeAlgebra_three_weight_le_four_pow_mul_apOfModel_of_exists_prime_dvd_mod_three_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_weight_le_succ_pow_mul_of_pow_mul_of_exists_prime_dvd_mod_three_eq_two
p2m_attr_erase "instance" "HeckeEis.instFiniteProjLineCusps ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.instIsElliptic_tateBase FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow HeckeEis.instAddCommGroupCoeffH1 HeckeEis.instModuleCoeffH1 CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk ModularCurve.ProjectiveLine.map_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModPForms.SSDatum.mk.sizeOf_spec ModPForms.SSDatum.mk.injEq ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.serrePairing_apply_mk AlgebraicCurve.residueSumOffChartLinear_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HeckeEis.binaryFormRep_apply_coe ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

p2m_open "CuspForm ModularForm UpperHalfPlane CongruenceSubgroup~one_mem_strictPeriods_Gamma0 ModPForms"
open scoped MatrixGroups

namespace WindowDock

section QCoeff

variable {N' : ℕ} {k' : ℤ}

private lemma T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  simp [Gamma0_mem, ModularGroup.coe_T]

private lemma one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

private lemma analyticAt_cusp (f : CuspForm (Gamma0 N') k') : AnalyticAt ℂ (cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma0 N')

private lemma qCoeff_add_cusp (f g : CuspForm (Gamma0 N') k') (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n = ModularFormClass.qCoeff ⇑f n + ModularFormClass.qCoeff ⇑g n := by
  simp only [ModularFormClass.qCoeff, CuspForm.coe_add, qExpansion_add (analyticAt_cusp f) (analyticAt_cusp g),
    map_add]

private lemma qCoeff_smul_cusp (c : ℂ) (f : CuspForm (Gamma0 N') k') (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) n = c * ModularFormClass.qCoeff ⇑f n := by
  simp only [ModularFormClass.qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analyticAt_cusp f) c, map_smul,
    smul_eq_mul]

private lemma qCoeff_zero_fun (n : ℕ) : ModularFormClass.qCoeff (0 : UpperHalfPlane → ℂ) n = 0 := by
  simp only [ModularFormClass.qCoeff, qExpansion_zero, map_zero]

private lemma qCoeff_zero_cusp (n : ℕ) : ModularFormClass.qCoeff (⇑(0 : CuspForm (Gamma0 N') k')) n = 0 := by
  rw [CuspForm.coe_zero, qCoeff_zero_fun]

end QCoeff

section Compat

variable {N' : ℕ} {k' : ℤ} (F : Type) [Field F]

private def IsIntPair (f : CuspForm (Gamma0 N') k') (a : ℕ → ℤ) : Prop :=
  ∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)

private lemma IsIntPair.unique {f : CuspForm (Gamma0 N') k'} {a b : ℕ → ℤ} (ha : IsIntPair f a) (hb : IsIntPair f b) :
    a = b :=
  funext fun n => Int.cast_injective (α := ℂ) ((ha n).symm.trans (hb n))

private noncomputable def redPS (a : ℕ → ℤ) : PowerSeries F :=
  PowerSeries.mk fun n => ((a n : ℤ) : F)

@[scoped simp] private lemma coeff_redPS (a : ℕ → ℤ) (n : ℕ) : PowerSeries.coeff n (redPS F a) = ((a n : ℤ) : F) := by
  simp [redPS]

private noncomputable def heckePSₗ (k : ℤ) (ℓ : ℕ) : PowerSeries F →ₗ[F] PowerSeries F where
  toFun := heckePS k ℓ
  map_add' φ ψ := by
    ext n
    simp only [heckePS, PowerSeries.coeff_mk, map_add]
    split_ifs <;> ring
  map_smul' c φ := by
    ext n
    simp only [heckePS, PowerSeries.coeff_mk, map_smul, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[scoped simp] private lemma heckePSₗ_apply (k : ℤ) (ℓ : ℕ) (φ : PowerSeries F) : heckePSₗ F k ℓ φ = heckePS k ℓ φ := rfl

private noncomputable def heckeUPSₗ (q : ℕ) : PowerSeries F →ₗ[F] PowerSeries F where
  toFun ψ := PowerSeries.mk fun n => PowerSeries.coeff (n * q) ψ
  map_add' φ ψ := by ext n; simp
  map_smul' c φ := by ext n; simp

private def Compat (x : Module.End ℂ (CuspForm (Gamma0 N') k')) : Prop :=
  ∃ Φ : PowerSeries F →ₗ[F] PowerSeries F,
    ∀ (f : CuspForm (Gamma0 N') k') (a : ℕ → ℤ), IsIntPair f a →
      ∃ b : ℕ → ℤ, IsIntPair (x f) b ∧ redPS F b = Φ (redPS F a)

variable {F}

private lemma compat_add {x y : Module.End ℂ (CuspForm (Gamma0 N') k')} (hx : Compat F x) (hy : Compat F y) :
    Compat F (x + y) := by
  obtain ⟨Φ, hΦ⟩ := hx
  obtain ⟨Ψ, hΨ⟩ := hy
  refine ⟨Φ + Ψ, fun f a ha => ?_⟩
  obtain ⟨b, hb, hbe⟩ := hΦ f a ha
  obtain ⟨b', hb', hbe'⟩ := hΨ f a ha
  refine ⟨b + b', fun n => ?_, ?_⟩
  · rw [LinearMap.add_apply, qCoeff_add_cusp, hb n, hb' n, Pi.add_apply, Int.cast_add]
  · rw [LinearMap.add_apply, ← hbe, ← hbe']
    ext n
    simp

private lemma compat_mul {x y : Module.End ℂ (CuspForm (Gamma0 N') k')} (hx : Compat F x) (hy : Compat F y) :
    Compat F (x * y) := by
  obtain ⟨Φ, hΦ⟩ := hx
  obtain ⟨Ψ, hΨ⟩ := hy
  refine ⟨Φ ∘ₗ Ψ, fun f a ha => ?_⟩
  obtain ⟨b, hb, hbe⟩ := hΨ f a ha
  obtain ⟨b', hb', hbe'⟩ := hΦ (y f) b hb
  exact ⟨b', fun n => by rw [Module.End.mul_apply]; exact hb' n, by rw [LinearMap.comp_apply, ← hbe, ← hbe']⟩

private lemma compat_smul (c : ℤ) : Compat F (N' := N') (k' := k') (algebraMap ℤ _ c) := by
  refine ⟨(c : F) • LinearMap.id, fun f a ha => ⟨fun n => c * a n, fun n => ?_, ?_⟩⟩
  · have h1 : (algebraMap ℤ (Module.End ℂ (CuspForm (Gamma0 N') k')) c) f = (c : ℂ) • f := by
      rw [algebraMap_int_eq, eq_intCast, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
    rw [h1, qCoeff_smul_cusp, ha n, Int.cast_mul]
  · ext n
    simp

private lemma intPair_T (hk' : 1 ≤ k') {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (f : CuspForm (Gamma0 N') k') (a : ℕ → ℤ) (ha : IsIntPair f a) :
    ∃ b : ℕ → ℤ, IsIntPair ((CuspForm.heckeTLin k' hℓ hℓN : Module.End ℂ _) f) b ∧
      redPS F b = heckePS k' ℓ (redPS F a) := by
  have hz : (((k' - 1).toNat : ℕ) : ℤ) = k' - 1 := Int.toNat_of_nonneg (by omega)
  have hpowC : (ℓ : ℂ) ^ (k' - 1) = (ℓ : ℂ) ^ (k' - 1).toNat := by rw [← zpow_natCast, hz]
  have hpowF : (ℓ : F) ^ (k' - 1) = (ℓ : F) ^ (k' - 1).toNat := by rw [← zpow_natCast, hz]
  refine ⟨fun n => a (n * ℓ) + if ℓ ∣ n then (ℓ : ℤ) ^ (k' - 1).toNat * a (n / ℓ) else 0, fun n => ?_, ?_⟩
  · have h1 := ModularFormClass.qCoeff_heckeT f (one_mem_strictPeriods_Gamma0 N') hℓ.ne_zero n
    rw [show ((CuspForm.heckeTLin k' hℓ hℓN : Module.End ℂ _) f : UpperHalfPlane → ℂ) =
      ModularForm.heckeT k' ℓ ⇑f from CuspForm.coe_heckeTLin_apply k' hℓ hℓN f, h1]
    simp only [ModularForm.coeffHeckeT, ha (n * ℓ), ha (n / ℓ), hpowC]
    split_ifs with h
    · push_cast
      ring
    · push_cast
      ring
  · ext n
    simp only [coeff_redPS, heckePS, PowerSeries.coeff_mk, hpowF]
    split_ifs with h
    · push_cast
      ring
    · push_cast
      ring

private lemma compat_T (hk' : 1 ≤ k') {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') :
    Compat F (N' := N') (k' := k') (CuspForm.heckeTLin k' hℓ hℓN) :=
  ⟨heckePSₗ F k' ℓ, fun f a ha => intPair_T hk' hℓ hℓN f a ha⟩

private lemma compat_U [NeZero N'] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N') :
    Compat F (N' := N') (k' := k') (CuspForm.heckeULin k' hqN) := by
  refine ⟨heckeUPSₗ F q, fun f a ha => ⟨fun n => a (n * q), fun n => ?_, ?_⟩⟩
  · have h1 := ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods_Gamma0 N') hq.ne_zero n (k := k')
    rw [show ((CuspForm.heckeULin k' hqN : Module.End ℂ _) f : UpperHalfPlane → ℂ) =
      ModularForm.heckeU k' q ⇑f from CuspForm.coe_heckeULin_apply k' hqN f, h1]
    simp only [ModularForm.coeffHeckeU, ha (n * q)]
  · ext n
    simp [heckeUPSₗ]

private lemma compat_of_mem [NeZero N'] (hk' : 1 ≤ k') (S₀ : Set ℕ)
    {x : Module.End ℂ (CuspForm (Gamma0 N') k')} (hx : x ∈ heckeAlgebra N' k' S₀) : Compat F x := by
  change x ∈ Algebra.adjoin ℤ (heckeGenerators N' k' S₀) at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩
    · exact compat_T hk' hℓ hℓN
    · exact compat_U hq hqN
  | algebraMap r => exact compat_smul r
  | add x y _ _ ihx ihy => exact compat_add ihx ihy
  | mul x y _ _ ihx ihy => exact compat_mul ihx ihy

end Compat

private theorem dictOut (p : ℕ) [Fact p.Prime]
    (N' : ℕ) [NeZero N'] (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (k' : ℤ) (hk' : 2 ≤ k')
    (φ : PowerSeries (AlgebraicClosure (ZMod p))) (lam : ℕ → AlgebraicClosure (ZMod p))
    (hφ : φ ∈ modPCusp N' k' (AlgebraicClosure (ZMod p))) (heig : IsModPEigen N' S₀ k' φ lam)
    (c : ℕ → ℤ) (good : ℕ → Prop)
    (hc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → good ℓ → lam ℓ = ((c ℓ : ℤ) : AlgebraicClosure (ZMod p))) :
    ∃ 𝔪' : Ideal (heckeAlgebra N' k' S₀), 𝔪'.IsMaximal ∧
      (p : heckeAlgebra N' k' S₀) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'), good ℓ →
        heckeAlgebra.T hℓ hℓN hℓS - ((c ℓ : ℤ) : heckeAlgebra N' k' S₀) ∈ 𝔪' := by
  classical
  have _ := hS₀p
  haveI : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_ringHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
  have hk1 : 1 ≤ k' := by omega

  let G : Set (heckeAlgebra N' k' S₀) :=
    {x | x = (p : heckeAlgebra N' k' S₀) ∨ ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      good ℓ ∧ x = heckeAlgebra.T hℓ hℓN hℓS - ((c ℓ : ℤ) : heckeAlgebra N' k' S₀)}
  let I : Ideal (heckeAlgebra N' k' S₀) := Ideal.span G

  have hP : ∀ y ∈ I, ∃ Φ : PowerSeries (AlgebraicClosure (ZMod p)) →ₗ[AlgebraicClosure (ZMod p)]
      PowerSeries (AlgebraicClosure (ZMod p)),
      (∀ (f : CuspForm (Gamma0 N') k') (a : ℕ → ℤ), IsIntPair f a →
        ∃ b : ℕ → ℤ, IsIntPair ((y : Module.End ℂ (CuspForm (Gamma0 N') k')) f) b ∧
          redPS (AlgebraicClosure (ZMod p)) b = Φ (redPS (AlgebraicClosure (ZMod p)) a)) ∧ Φ φ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with rfl | ⟨ℓ, hℓ, hℓS, hℓN, hg, rfl⟩
      · refine ⟨0, fun f a ha => ⟨fun n => p * a n, fun n => ?_, ?_⟩, by simp⟩
        · have h1 : ((p : heckeAlgebra N' k' S₀) : Module.End ℂ (CuspForm (Gamma0 N') k')) f =
              ((p : ℤ) : ℂ) • f := by
            rw [show ((p : heckeAlgebra N' k' S₀) : Module.End ℂ (CuspForm (Gamma0 N') k')) =
              (p : Module.End ℂ (CuspForm (Gamma0 N') k')) from map_natCast (heckeAlgebra N' k' S₀).val p,
              Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul ℂ, Int.cast_natCast]
          rw [h1, qCoeff_smul_cusp, ha n]
          push_cast
          ring
        · ext n
          simp [CharP.cast_eq_zero]
      · refine ⟨heckePSₗ _ k' ℓ - ((c ℓ : ℤ) : AlgebraicClosure (ZMod p)) • LinearMap.id, fun f a ha => ?_, ?_⟩
        · obtain ⟨b, hb, hbe⟩ := intPair_T (F := AlgebraicClosure (ZMod p)) hk1 hℓ hℓN f a ha
          refine ⟨fun n => b n - c ℓ * a n, fun n => ?_, ?_⟩
          · have h1 : ((heckeAlgebra.T hℓ hℓN hℓS - ((c ℓ : ℤ) : heckeAlgebra N' k' S₀) : heckeAlgebra N' k' S₀) :
                Module.End ℂ (CuspForm (Gamma0 N') k')) f =
                (CuspForm.heckeTLin k' hℓ hℓN : Module.End ℂ _) f + (-(c ℓ : ℂ)) • f := by
              rw [show ((heckeAlgebra.T hℓ hℓN hℓS - ((c ℓ : ℤ) : heckeAlgebra N' k' S₀) :
                  heckeAlgebra N' k' S₀) : Module.End ℂ (CuspForm (Gamma0 N') k')) =
                  (CuspForm.heckeTLin k' hℓ hℓN : Module.End ℂ _) - ((c ℓ : ℤ) : Module.End ℂ _) by
                rw [← Subalgebra.coe_val, map_sub, map_intCast, Subalgebra.coe_val]; rfl,
                LinearMap.sub_apply, Module.End.intCast_apply, sub_eq_add_neg, ← neg_zsmul,
                ← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg]
            rw [h1, qCoeff_add_cusp, qCoeff_smul_cusp, hb n, ha n]
            push_cast
            ring
          · ext n
            simp only [coeff_redPS, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
              map_smul, smul_eq_mul, heckePSₗ_apply, ← hbe, coeff_redPS]
            push_cast
            ring
        · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, heckePSₗ_apply,
            heig.2 ℓ hℓ hℓN hℓS, hc ℓ hℓ hℓS hℓN hg, sub_self]
    | zero =>
      exact ⟨0, fun f a ha => ⟨0, fun n => by simp [qCoeff_zero_fun], by ext n; simp⟩, by simp⟩
    | add y z _ _ ihy ihz =>
      obtain ⟨Φ, hΦ, hΦ0⟩ := ihy
      obtain ⟨Ψ, hΨ, hΨ0⟩ := ihz
      refine ⟨Φ + Ψ, fun f a ha => ?_, by simp [hΦ0, hΨ0]⟩
      obtain ⟨b, hb, hbe⟩ := hΦ f a ha
      obtain ⟨b', hb', hbe'⟩ := hΨ f a ha
      refine ⟨b + b', fun n => ?_, ?_⟩
      · rw [Subalgebra.coe_add, LinearMap.add_apply, qCoeff_add_cusp, hb n, hb' n, Pi.add_apply, Int.cast_add]
      · rw [LinearMap.add_apply, ← hbe, ← hbe']
        ext n
        simp
    | smul x y _ ihy =>
      obtain ⟨Ψ, hΨ, hΨ0⟩ := ihy
      obtain ⟨Φ, hΦ⟩ := compat_of_mem (F := AlgebraicClosure (ZMod p)) hk1 S₀ x.2
      refine ⟨Φ ∘ₗ Ψ, fun f a ha => ?_, by simp [hΨ0]⟩
      obtain ⟨b, hb, hbe⟩ := hΨ f a ha
      obtain ⟨b', hb', hbe'⟩ := hΦ _ b hb
      refine ⟨b', fun n => ?_, by rw [LinearMap.comp_apply, ← hbe, ← hbe']⟩
      rw [smul_eq_mul, Subalgebra.coe_mul, Module.End.mul_apply]
      exact hb' n

  have hI : I ≠ ⊤ := by
    intro htop
    obtain ⟨Φ, hΦ, hΦ0⟩ := hP 1 (htop ▸ Submodule.mem_top)
    have hgen : ∀ ψ ∈ {φ | ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N') k') (a : ℕ → ℤ),
        (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧
          φ = PowerSeries.mk fun n => ((a n : ℤ) : AlgebraicClosure (ZMod p))}, Φ ψ = ψ := by
      rintro ψ ⟨f, a, ha, rfl⟩
      obtain ⟨b, hb, hbe⟩ := hΦ f a ha
      have hb' : IsIntPair f b := fun n => by simpa [Subalgebra.coe_one] using hb n
      obtain rfl := IsIntPair.unique ha hb'
      exact hbe.symm
    have hfix : Φ φ = φ := by
      have hle : modPCusp N' k' (AlgebraicClosure (ZMod p)) ≤ LinearMap.eqLocus Φ LinearMap.id :=
        Submodule.span_le.mpr fun ψ hψ => hgen ψ hψ
      exact hle hφ
    exact heig.1 (by rw [← hfix, hΦ0])
  obtain ⟨𝔪', h𝔪', hI𝔪'⟩ := Ideal.exists_le_maximal I hI
  refine ⟨𝔪', h𝔪', hI𝔪' (Ideal.subset_span (Or.inl rfl)), fun ℓ hℓ hℓS hℓN hg => ?_⟩
  exact hI𝔪' (Ideal.subset_span (Or.inr ⟨ℓ, hℓ, hℓS, hℓN, hg, rfl⟩))

private lemma five_le {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  by_contra h
  rw [not_le] at h
  interval_cases p
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact h2 rfl
  · exact h3 rfl
  · exact absurd hp (by decide)

end WindowDock
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_weight_le_succ_pow_mul_of_pow_mul_of_exists_prime_dvd_mod_three_eq_two.WindowDock"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (hq3 : p = 3 → ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k : ℤ) (hk : 2 ≤ k) (i : ℕ) (𝔪ₖ : Ideal (heckeAlgebra N' k S₀)) (h𝔪ₖ : 𝔪ₖ.IsMaximal)
    (hp𝔪ₖ : (p : heckeAlgebra N' k S₀) ∈ 𝔪ₖ)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        heckeAlgebra.T hℓ hℓN hℓS -
          ((ℓ ^ i * W.apOfModel ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪ₖ) :
    ∃ k' : ℤ, 2 ≤ k' ∧ k' ≤ (p : ℤ) + 1 ∧ ∃ j : ℕ,
      ∃ 𝔪' : Ideal (heckeAlgebra N' k' S₀), 𝔪'.IsMaximal ∧
        (p : heckeAlgebra N' k' S₀) ∈ 𝔪' ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
          W.IsGoodPrimeFor ℓ →
            heckeAlgebra.T hℓ hℓN hℓS -
              ((ℓ ^ j * W.apOfModel ℓ : ℤ) : heckeAlgebra N' k' S₀) ∈ 𝔪' := by
  classical
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨k', hk'2, hk'4, j, 𝔪', hmax, h3, hT⟩ :=
      W.exists_ideal_heckeAlgebra_three_weight_le_four_pow_mul_apOfModel_of_exists_prime_dvd_mod_three_eq_two
        hΔ hirr N' hpN' (hq3 rfl) S₀ hS₀fin hS₀p k hk i 𝔪ₖ h𝔪ₖ (by simpa using hp𝔪ₖ) hocc
    exact ⟨k', hk'2, by push_cast; omega, j, 𝔪', hmax, by simpa using h3, hT⟩
  · have hpf : p.Prime := Fact.out
    have hp5 : 5 ≤ p := WindowDock.five_le hpf hp2 hp3
    haveI : CharP (AlgebraicClosure (ZMod p)) p :=
      charP_of_injective_ringHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
    obtain ⟨φ, lam, hφ, heig, hlam⟩ :=
      WeierstrassCurve.exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra p W N' S₀ hS₀p k hk
        (CuspForm.hasIntegralStructure_of_two_le N' k hk) i 𝔪ₖ h𝔪ₖ hp𝔪ₖ hocc
    obtain ⟨k', hk'2, hk'p, j, ψ, mu, hψ, heigψ, hmu⟩ :=
      ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure p hp5 N' hpN' S₀
        hS₀fin hS₀p k hk φ lam
        (ModPForms.modPCusp_le_modPMod N' k (AlgebraicClosure (ZMod p)) hφ) heig
    have hmu' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
        mu ℓ = ((ℓ ^ (i + j) * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) := by
      intro ℓ hℓ hℓS hℓN hgood
      rw [hmu ℓ hℓ hℓN hℓS, hlam ℓ hℓ hℓS hℓN hgood]
      push_cast
      ring
    obtain ⟨ψ', mu', hψ', heig', hmu''⟩ :=
      WeierstrassCurve.exists_mem_modPCusp_isModPEigen_of_mem_modPMod_of_modRepIsIrreducible p hp5 W hΔ hirr N' hpN'
        S₀ hS₀fin hS₀p k' hk'2 (i + j) ψ mu hψ heigψ hmu'
    refine ⟨k', hk'2, hk'p, i + j, ?_⟩
    exact WindowDock.dictOut p N' S₀ hS₀p k' hk'2 ψ' mu' hψ' heig' (fun ℓ => ℓ ^ (i + j) * W.apOfModel ℓ)
      W.IsGoodPrimeFor hmu''

end S_WeierstrassCurve_exists_ideal_heckeAlgebra_weight_le_succ_pow_mul_of_pow_mul_of_exists_prime_dvd_mod_three_eq_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_weight_le_succ_pow_mul_of_pow_mul_of_exists_prime_dvd_mod_three_eq_two (solution)
