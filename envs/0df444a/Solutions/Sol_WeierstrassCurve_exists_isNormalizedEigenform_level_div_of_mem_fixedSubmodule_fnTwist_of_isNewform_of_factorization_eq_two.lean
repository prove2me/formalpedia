-- Prove2me | solution 1 for WeierstrassCurve.exists_isNormalizedEigenform_level_div_of_mem_fixedSubmodule_fnTwist_of_isNewform_of_factorization_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2bb180fd-1c34-587a-ab30-7b69de65ec17

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_WeierstrassCurve_exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra
import Theorems.Thm_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_HeckeCharacter_IsFiniteOrderHeckeChar_exists_dirichletIdeleChar_eq_of_admitsModulus
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.CharP.Lemmas
import Definitions.Def_CohCarrier_Inst
import Theorems.Thm_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Matrix.ToLin
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isOdd
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_restrict_index_two
import Theorems.Thm_WeierstrassCurve_IsIntegralModelOf_galoisTrace_det_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_mem_fixedSubmodule_fnTwist_of_isNewform_of_factorization_eq_two
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq WeierstrassCurve.Affine.mem_fibSet FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

section

open NumberField IsDedekindDomain

namespace LevelLowering

section Level

variable {L q : ℕ}

private theorem prime_dvd_of_factorization_eq_two (hq2 : L.factorization q = 2) : q ∣ L :=
  Nat.dvd_of_factorization_pos (by rw [hq2]; exact two_ne_zero)

private theorem ne_zero_of_factorization_eq_two (hq2 : L.factorization q = 2) : L ≠ 0 := by
  rintro rfl
  rw [Nat.factorization_zero, Finsupp.zero_apply] at hq2
  exact two_ne_zero hq2.symm

private theorem div_ne_zero_of_factorization_eq_two (hq2 : L.factorization q = 2) : L / q ≠ 0 := by
  intro h
  have hL : L = q * (L / q) := (Nat.mul_div_cancel' (prime_dvd_of_factorization_eq_two hq2)).symm
  rw [h, mul_zero] at hL
  exact ne_zero_of_factorization_eq_two hq2 hL

private theorem div_dvd_of_factorization_eq_two {M : ℕ} (hq2 : L.factorization q = 2) (hLM : L ∣ M) : L / q ∣ M :=
  (Nat.div_dvd_of_dvd (prime_dvd_of_factorization_eq_two hq2)).trans hLM

private theorem factorization_div_of_factorization_eq_two (hq : q.Prime) (hq2 : L.factorization q = 2) :
    (L / q).factorization q = 1 := by
  rw [Nat.factorization_div (prime_dvd_of_factorization_eq_two hq2), Finsupp.tsub_apply, hq2,
    Nat.Prime.factorization_self hq]

private theorem prime_dvd_div_of_factorization_eq_two (hq : q.Prime) (hq2 : L.factorization q = 2) : q ∣ L / q :=
  Nat.dvd_of_factorization_pos (by rw [factorization_div_of_factorization_eq_two hq hq2]; exact one_ne_zero)

private theorem ne_of_not_dvd_of_factorization_eq_two (hq2 : L.factorization q = 2) {ℓ : ℕ} (h : ¬ ℓ ∣ L) : ℓ ≠ q := by
  rintro rfl
  exact h (prime_dvd_of_factorization_eq_two hq2)

private theorem ne_zero_and_div_ne_zero_and_div_dvd_and_dvd_div {M : ℕ} [Fact q.Prime] (hq2 : L.factorization q = 2)
    (hLM : L ∣ M) : L ≠ 0 ∧ L / q ≠ 0 ∧ L / q ∣ M ∧ q ∣ L / q :=
  ⟨ne_zero_of_factorization_eq_two hq2, div_ne_zero_of_factorization_eq_two hq2,
    div_dvd_of_factorization_eq_two hq2 hLM, prime_dvd_div_of_factorization_eq_two Fact.out hq2⟩

private theorem exists_units_coe_eq_lowerRight_of_dvd [Fact q.Prime] {N : ℕ} (hqN : q ∣ N)
    (σ : CongruenceSubgroup.Gamma0 N) :
    ∃ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) =
      ((((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ_[q]) := by
  have hc : ((N : ℕ) : ℤ) ∣ ((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp σ.2)
  have hdet := Matrix.SpecialLinearGroup.det_coe (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
  rw [Matrix.det_fin_two] at hdet
  have hnot : ¬ ((q : ℕ) : ℤ) ∣ ((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
    intro hd
    have hqN' : ((q : ℕ) : ℤ) ∣ ((N : ℕ) : ℤ) := by exact_mod_cast hqN
    have h1 : ((q : ℕ) : ℤ) ∣ 1 := by
      rw [← hdet]
      exact dvd_sub (hd.mul_left _) ((hqN'.trans hc).mul_left _)
    have h1' : q ∣ 1 := by exact_mod_cast h1
    exact (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp h1')
  have hnorm : ‖((((σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℤ_[q])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp fun hlt => hnot ((PadicInt.norm_int_lt_one_iff_dvd _).mp hlt))
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.mpr hnorm
  exact ⟨u, by rw [hu, PadicInt.coe_intCast]⟩

end Level

section RootsOfUnity

private theorem exists_integralClosure_coe_eq_and_sub_one_mem_of_pow_prime_pow_eq_one (p : ℕ) [Fact p.Prime]
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (c : ℂ) (k : ℕ) (hc : c ^ p ^ k = 1) :
    ∃ ζ : integralClosure ℤ ℂ, (ζ : ℂ) = c ∧ ζ - 1 ∈ 𝔪 := by
  have hint : IsIntegral ℤ c :=
    IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos k) (by rw [hc]; exact isIntegral_one)
  let ζ : integralClosure ℤ ℂ := ⟨c, (mem_integralClosure_iff (R := ℤ) (A := ℂ)).mpr hint⟩
  refine ⟨ζ, rfl, ?_⟩
  have hζpow : ζ ^ p ^ k = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hc
  haveI := h𝔪
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  have hpK : ((p : ℕ) : integralClosure ℤ ℂ ⧸ 𝔪) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔪
    rwa [map_natCast] at h
  haveI : CharP (integralClosure ℤ ℂ ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpK
  have hz : Ideal.Quotient.mk 𝔪 ζ - 1 = 0 := by
    have h1 : (Ideal.Quotient.mk 𝔪 ζ - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, ← map_pow, hζpow, map_one, one_pow, sub_self]
    exact (pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero)).mp h1
  have h1 : Ideal.Quotient.mk 𝔪 ζ = Ideal.Quotient.mk 𝔪 1 := by
    rw [map_one]
    exact sub_eq_zero.mp hz
  exact Ideal.Quotient.eq.mp h1

end RootsOfUnity

section Uniformizer

variable (q : ℕ) [Fact q.Prime]

private noncomputable def unitIdeleAt (u : ℤ_[q]ˣ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
    (AdelicLevel.localUnit (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
      (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))

private theorem coe_component (u : ℤ_[q]ˣ) :
    ((Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u) :
        ((AdelicDock.padicPlace q).adicCompletion ℚ)ˣ) : (AdelicDock.padicPlace q).adicCompletion ℚ) =
      AdelicDock.padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) := by
  rw [Units.coe_map, Units.coe_map]
  rfl

private theorem valued_padicRingEquiv_coe_unit (u : ℤ_[q]ˣ) :
    Valued.v (AdelicDock.padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q])) = 1 := by
  have hle : ∀ w : ℤ_[q]ˣ, Valued.v (AdelicDock.padicRingEquiv q ((w : ℤ_[q]) : ℚ_[q])) ≤ 1 := fun w =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mp
      (AdelicDock.padicRingEquiv_coe_mem q (w : ℤ_[q]))
  have hmul : Valued.v (AdelicDock.padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q])) *
      Valued.v (AdelicDock.padicRingEquiv q (((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q])) = 1 := by
    rw [← map_mul, ← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one, map_one]
  refine le_antisymm (hle u) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmul.symm
    _ ≤ Valued.v (AdelicDock.padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q])) * 1 := mul_le_mul_right (hle u⁻¹) _
    _ = _ := mul_one _

private theorem unitAt_unitIdeleAt (u : ℤ_[q]ˣ) :
    RatIdele.unitAt (AdelicDock.padicPlace q) (unitIdeleAt q u) =
      AdelicDock.padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) := by
  have ht : Valued.v
      ((Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u) :
        ((AdelicDock.padicPlace q).adicCompletion ℚ)ˣ) : (AdelicDock.padicPlace q).adicCompletion ℚ) = 1 := by
    rw [coe_component]
    exact valued_padicRingEquiv_coe_unit q u
  unfold unitIdeleAt
  rw [RatIdele.unitAt_finIncl_localUnit_self _ _ ht, coe_component]

private theorem exists_units_coe_eq_natCast {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) :
    ∃ u : ℤ_[q]ˣ, (u : ℤ_[q]) = (ℓ : ℤ_[q]) := by
  have hnorm : ‖(ℓ : ℤ_[q])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
    have hdvd : ((q : ℕ) : ℤ) ∣ ((ℓ : ℕ) : ℤ) := (PadicInt.norm_int_lt_one_iff_dvd _).mp (by exact_mod_cast hlt)
    have hqℓ : q ∣ ℓ := by exact_mod_cast hdvd
    exact hℓq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hℓ).mp hqℓ).symm
  exact PadicInt.isUnit_iff.mpr hnorm

private theorem natGenerator_padicPlace (ℓ : ℕ) [Fact ℓ.Prime] :
    Rat.HeightOneSpectrum.natGenerator (AdelicDock.padicPlace ℓ) = ℓ :=
  RatIdele.natGenerator_primesEquiv_symm ⟨ℓ, Fact.out⟩

private theorem eq_padicPlace_of_natGenerator_dvd {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : Rat.HeightOneSpectrum.natGenerator w ∣ q) : w = AdelicDock.padicPlace q := by
  refine RatIdele.eq_of_natGenerator_eq ?_
  rw [natGenerator_padicPlace]
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) (Fact.out : q.Prime)).mp hw

variable {q} [NeZero q]

private theorem coe_dirichletIdeleChar_unitIdeleAt_inv (χ : DirichletCharacter ℂ q) {ℓ : ℕ}
    {u : ℤ_[q]ˣ} (hu : (u : ℤ_[q]) = (ℓ : ℤ_[q])) :
    ((χ.dirichletIdeleChar (unitIdeleAt q u⁻¹) : ℂˣ) : ℂ) = χ ((ℓ : ℕ) : ZMod q) := by
  have hres : ((ℓ : ℕ) : ZMod q) * RatIdele.unitResidue q (unitIdeleAt q u⁻¹) = 1 := by
    refine RatIdele.natCast_mul_unitResidue_eq_one q fun w hw => ?_
    obtain rfl := eq_padicPlace_of_natGenerator_dvd q hw
    have hℓ' : ((ℓ : ℕ) : (AdelicDock.padicPlace q).adicCompletion ℚ) =
        AdelicDock.padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) := by
      rw [hu, PadicInt.coe_natCast, map_natCast]
    rw [unitAt_unitIdeleAt, hℓ', ← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one]
  have hχ : χ ((ℓ : ℕ) : ZMod q) * χ (RatIdele.unitResidue q (unitIdeleAt q u⁻¹)) = 1 := by
    rw [← map_mul, hres, map_one]
  rw [DirichletCharacter.coe_dirichletIdeleChar_apply]
  exact (eq_inv_of_mul_eq_one_left hχ).symm

private theorem coe_dirichletIdeleChar_uniformizerIdele (χ : DirichletCharacter ℂ q) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓq : ℓ ≠ q) :
    ((χ.dirichletIdeleChar (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂˣ) : ℂ) =
      χ ((ℓ : ℕ) : ZMod q) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hv : ¬ Rat.HeightOneSpectrum.natGenerator (AdelicDock.padicPlace ℓ) ∣ q := by
    rw [natGenerator_padicPlace]
    exact fun h => hℓq ((Nat.prime_dvd_prime_iff_eq hℓ (Fact.out : q.Prime)).mp h)
  have h := DirichletCharacter.coe_dirichletIdeleChar_finIncl_localUnit_of_valued_exp_neg_one χ hv
    (AdelicLevel.uniformizerUnit ℚ (AdelicDock.padicPlace ℓ))
    (AdelicLevel.valued_uniformizerUnit ℚ (AdelicDock.padicPlace ℓ))
  rw [natGenerator_padicPlace] at h
  exact h

end Uniformizer

section Values

variable (p : ℕ) {L : ℕ} {q : ℕ}

private theorem apply_uniformizerIdele_pow_prime_pow_eq_one (hq2 : L.factorization q = 2) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel q))
    (hηp : ∀ u : ℤ_[q]ˣ, ∃ n : ℕ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) ^ p ^ n = 1) :
    ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ L →
      ∃ n : ℕ, η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) ^ p ^ n = 1 := by
  intro ℓ hℓ hℓL
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hℓq : ℓ ≠ q := ne_of_not_dvd_of_factorization_eq_two hq2 hℓL
  have hmod : HeckeCharacter.AdmitsModulus ℚ η (Ideal.span {((q : ℕ) : 𝓞 ℚ)}) := hηmod
  obtain ⟨χ, hχ⟩ := hηfin.exists_dirichletIdeleChar_eq_of_admitsModulus hmod
  obtain ⟨u, hu⟩ := exists_units_coe_eq_natCast q hℓ hℓq
  obtain ⟨n, hn⟩ := hηp u⁻¹
  refine ⟨n, ?_⟩
  have hval : η (unitIdeleAt q u⁻¹) = η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) := by
    refine Units.ext ?_
    rw [← hχ, coe_dirichletIdeleChar_unitIdeleAt_inv χ hu, coe_dirichletIdeleChar_uniformizerIdele χ hℓ hℓq]
  rw [← hval]
  exact hn

private theorem coe_apply_uniformizerIdele_pow_prime_pow_eq_one (hq2 : L.factorization q = 2) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel q))
    (hηp : ∀ u : ℤ_[q]ˣ, ∃ n : ℕ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) ^ p ^ n = 1) :
    ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ L →
      ∃ n : ℕ, (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) ^ p ^ n = 1 := by
  intro ℓ hℓ hℓL
  obtain ⟨n, hn⟩ := apply_uniformizerIdele_pow_prime_pow_eq_one p hq2 η hηfin hηmod hηp ℓ hℓ hℓL
  exact ⟨n, by rw [← Units.val_pow_eq_pow_val, hn, Units.val_one]⟩

private theorem exists_integralClosure_coe_eq_apply_uniformizerIdele_and_sub_one_mem [Fact p.Prime]
    (hq2 : L.factorization q = 2) [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel q))
    (hηp : ∀ u : ℤ_[q]ˣ, ∃ n : ℕ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) ^ p ^ n = 1)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ L →
      ∃ ζ : integralClosure ℤ ℂ,
        (ζ : ℂ) = (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) ∧ ζ - 1 ∈ 𝔪 := by
  intro ℓ hℓ hℓL
  obtain ⟨n, hn⟩ := coe_apply_uniformizerIdele_pow_prime_pow_eq_one p hq2 η hηfin hηmod hηp ℓ hℓ hℓL
  exact exists_integralClosure_coe_eq_and_sub_one_mem_of_pow_prime_pow_eq_one p 𝔪 h𝔪 hp𝔪 _ n hn

private theorem inv_sq_coe_apply_pow_prime_pow_eq_one [Fact q.Prime]
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηp : ∀ u : ℤ_[q]ˣ, ∃ n : ℕ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) ^ p ^ n = 1) :
    ∀ u : ℤ_[q]ˣ, ∃ n : ℕ,
      ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
              (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2)⁻¹ ^ p ^ n = 1 := by
  intro u
  obtain ⟨n, hn⟩ := hηp u
  refine ⟨n, ?_⟩
  have hx : (η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
      (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
        (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
          (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ p ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hn, Units.val_one]
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hx, one_pow, inv_one]

end Values

end LevelLowering
end

section

open scoped MatrixGroups

namespace LevelLowering

open CohCarrier CongruenceSubgroup

private theorem gamma_le_gammaH (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    Gamma N ≤ GammaH N H := by
  intro A hA
  rw [Gamma_mem] at hA
  obtain ⟨-, -, h10, h11⟩ := hA
  have hA0 : A ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact h10
  rw [mem_GammaH_iff]
  refine ⟨hA0, ?_⟩
  have h1 : gamma0Units N ⟨A, hA0⟩ = 1 := by
    ext
    simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [h1]
  exact one_mem H

private theorem finiteIndex_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    (GammaH N H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma_le_gammaH N H)

private theorem trace_coe_conj (a z : SL(2, ℤ)) :
    ((a * z * a⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      (z : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel_left]

private theorem trace_coe_inv_conj (a z : SL(2, ℤ)) :
    ((a⁻¹ * z * a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      (z : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel_left]

private theorem trace_mul_mul_self {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = 1)
    (B : Matrix (Fin 2) (Fin 2) ℤ) : (B * (A * A)).trace = A.trace * (B * A).trace - B.trace := by
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-(B 0 0 + B 1 1)) * hdet

private theorem trace_pow_sq_eq_four {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = 1)
    (htr : A.trace ^ 2 = 4) (k : ℕ) : (A ^ k).trace ^ 2 = 4 := by
  have hrec : ∀ k : ℕ, (A ^ (k + 1 + 1)).trace = A.trace * (A ^ (k + 1)).trace - (A ^ k).trace := by
    intro k
    rw [pow_succ _ (k + 1), pow_succ _ k, mul_assoc, trace_mul_mul_self hdet]
  have h0 : (A ^ 0).trace = 2 := by
    rw [pow_zero, Matrix.trace_one, Fintype.card_fin]
    norm_num
  have hcases : A.trace = 2 ∨ A.trace = -2 := by
    have h : (A.trace - 2) * (A.trace + 2) = 0 := by linear_combination htr
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hcases with h2 | h2
  · have key : ∀ k : ℕ, (A ^ k).trace = 2 ∧ (A ^ (k + 1)).trace = 2 := by
      intro k
      induction k with
      | zero => exact ⟨h0, by rw [zero_add, pow_one, h2]⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rw [hrec, h2, ih.1, ih.2]
        norm_num
    rw [(key k).1]
    norm_num
  · have key : ∀ k : ℕ, (A ^ k).trace = 2 * (-1) ^ k ∧ (A ^ (k + 1)).trace = 2 * (-1) ^ (k + 1) := by
      intro k
      induction k with
      | zero =>
        refine ⟨?_, ?_⟩
        · rw [h0]
          norm_num
        · rw [zero_add, pow_one, h2]
          norm_num
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rw [hrec, h2, ih.1, ih.2]
        ring
    rw [(key k).1, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num

private theorem diamondRaw_mem_parabolicHoms (N : ℕ) (H : Subgroup (ZMod N)ˣ) {R A : Type*}
    [Semiring R] [AddCommGroup A] [Module R A] (σ : Gamma0 N) {φ : H1 N H A}
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms R (GammaH N H) A) :
    diamondRaw N H A σ φ ∈ ModularCurve.Period.parabolicHoms R (GammaH N H) A := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hφ ⊢
  intro γ hγ
  show φ (Additive.ofMul (conjHom N H σ γ)) = 0
  apply hφ
  show (((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [trace_coe_conj]
  exact hγ

private theorem trace_conjL (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) (y : ↥(GammaHUpper N H ℓ)) :
    (((conjL N H ℓ y : ↥(GammaH N H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((((y : ↥(GammaHUpper N H ℓ)) : ↥(GammaH N H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjL, conjUpperMat]

private theorem heckeT_mem_parabolicHoms (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {R A : Type*} [Semiring R] [AddCommGroup A] [Module R A] {φ : H1 N H A}
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms R (GammaH N H) A) :
    heckeT N H ℓ A φ ∈ ModularCurve.Period.parabolicHoms R (GammaH N H) A := by
  classical
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hφ ⊢
  intro g hg
  have key : ∀ (r : ↥(GammaH N H)) (k : ℕ),
      (((r⁻¹ * g ^ k * r : ↥(GammaH N H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
    intro r k
    have e : ((r⁻¹ * g ^ k * r : ↥(GammaH N H)) : SL(2, ℤ)) =
        (r : SL(2, ℤ))⁻¹ * (g : SL(2, ℤ)) ^ k * (r : SL(2, ℤ)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    rw [e, trace_coe_inv_conj, Matrix.SpecialLinearGroup.coe_pow]
    exact trace_pow_sq_eq_four (Matrix.SpecialLinearGroup.det_coe _) hg k
  show Multiplicative.toAdd
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL N H ℓ)) g) = 0
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g)
      (↥(GammaH N H) ⧸ GammaHUpper N H ℓ))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [MonoidHom.comp_apply, AddMonoidHom.coe_toMultiplicativeRight, Function.comp_apply,
    toAdd_ofAdd]
  apply hφ
  rw [trace_conjL]
  exact key _ _

private def diamondLin (N : ℕ) (H : Subgroup (ZMod N)ˣ) (R : Type) [CommRing R] (σ : Gamma0 N) :
    H1 N H R →ₗ[R] H1 N H R where
  toFun := diamondRaw N H R σ
  map_add' := map_add _
  map_smul' c φ := by
    ext
    rfl

private noncomputable def latticeMatrix (N : ℕ) (H : Subgroup (ZMod N)ˣ) {t : ℕ}
    (b : Module.Basis (Fin t) ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ))
    (T : H1 N H ℤ →+ H1 N H ℤ)
    (hT : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      T.toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ) :
    Matrix (Fin t) (Fin t) ℤ :=
  LinearMap.toMatrix b b (T.toIntLinearMap.restrict hT)

private theorem castAddHom_comp_sum_smul (N : ℕ) (H : Subgroup (ZMod N)ˣ) {ι : Type*}
    (s : Finset ι) (c : ι → ℤ) (ψ : ι → H1 N H ℤ) :
    (Int.castAddHom ℂ).comp (∑ i ∈ s, c i • ψ i) =
      ∑ i ∈ s, (c i : ℂ) • (Int.castAddHom ℂ).comp (ψ i) := by
  refine AddMonoidHom.ext fun x => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.smul_apply, Int.coe_castAddHom, smul_eq_mul, Int.cast_sum, Int.cast_mul]

private theorem toMatrix_restrict_eq_map (N : ℕ) (H : Subgroup (ZMod N)ˣ) {t : ℕ}
    (b : Module.Basis (Fin t) ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ))
    (bC : Module.Basis (Fin t) ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ))
    (hbC : ∀ i, (bC i : H1 N H ℂ) = (Int.castAddHom ℂ).comp (b i : H1 N H ℤ))
    (T : H1 N H ℤ →+ H1 N H ℤ)
    (hT : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      T.toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)
    (TC : H1 N H ℂ →ₗ[ℂ] H1 N H ℂ)
    (hTC : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ,
      TC ψ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ)
    (hnat : ∀ ψ : H1 N H ℤ, TC ((Int.castAddHom ℂ).comp ψ) = (Int.castAddHom ℂ).comp (T ψ)) :
    LinearMap.toMatrix bC bC (TC.restrict hTC) = (latticeMatrix N H b T hT).map (Int.cast : ℤ → ℂ) := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply]

  have hcolP : (T.toIntLinearMap.restrict hT) (b j) = ∑ i, latticeMatrix N H b T hT i j • b i := by
    simp_rw [latticeMatrix, LinearMap.toMatrix_apply]
    exact (b.sum_repr ((T.toIntLinearMap.restrict hT) (b j))).symm
  have hcolZ : T (b j : H1 N H ℤ) = ∑ i, latticeMatrix N H b T hT i j • (b i : H1 N H ℤ) := by
    have h2 := congrArg Subtype.val hcolP
    simpa only [LinearMap.coe_restrict_apply, AddMonoidHom.coe_toIntLinearMap, Submodule.coe_sum,
      Submodule.coe_smul] using h2

  have hcolC : TC (bC j : H1 N H ℂ) = ∑ i, (latticeMatrix N H b T hT i j : ℂ) • (bC i : H1 N H ℂ) := by
    rw [hbC j, hnat, hcolZ, castAddHom_comp_sum_smul]
    simp only [hbC]
  have h3 : TC.restrict hTC (bC j) = ∑ i, (latticeMatrix N H b T hT i j : ℂ) • bC i := by
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, hcolC, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [h3, bC.repr_sum_self]

private theorem map_latticeMatrix_mulVec_repr (N : ℕ) (H : Subgroup (ZMod N)ˣ) {t : ℕ}
    (b : Module.Basis (Fin t) ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ))
    (bC : Module.Basis (Fin t) ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ))
    (hbC : ∀ i, (bC i : H1 N H ℂ) = (Int.castAddHom ℂ).comp (b i : H1 N H ℤ))
    (T : H1 N H ℤ →+ H1 N H ℤ)
    (hT : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      T.toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)
    (TC : H1 N H ℂ →ₗ[ℂ] H1 N H ℂ)
    (hTC : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ,
      TC ψ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ)
    (hnat : ∀ ψ : H1 N H ℤ, TC ((Int.castAddHom ℂ).comp ψ) = (Int.castAddHom ℂ).comp (T ψ))
    (x : ↥(ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ)) (a : ℂ)
    (hx : TC x = a • (x : H1 N H ℂ)) :
    ((latticeMatrix N H b T hT).map (Int.cast : ℤ → ℂ)).mulVec ⇑(bC.repr x) = a • ⇑(bC.repr x) := by
  rw [← toMatrix_restrict_eq_map N H b bC hbC T hT TC hTC hnat, LinearMap.toMatrix_mulVec_repr]
  have h : TC.restrict hTC x = a • x := by
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, hx, Submodule.coe_smul]
  rw [h, map_smul, Finsupp.coe_smul]

private theorem not_exists_eq_natCast_smul (N : ℕ) (H : Subgroup (ZMod N)ˣ) {t : ℕ}
    (b : Module.Basis (Fin t) ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ))
    {p : ℕ} [NeZero p] (m : Fin t → ZMod p) (hm : m ≠ 0) (c : Fin t → ℤ)
    (hc : ∀ i, (c i : ZMod p) = m i) :
    ¬ ∃ ψ : H1 N H ℤ,
      ((∑ i, c i • b i : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)) : H1 N H ℤ) =
        (p : ℤ) • ψ := by
  rintro ⟨ψ, hψ⟩
  apply hm

  have hψP : ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ := by
    rw [ModularCurve.Period.mem_parabolicHoms_iff]
    intro γ hγ
    have hxP := (∑ i, c i • b i : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)).2
    rw [ModularCurve.Period.mem_parabolicHoms_iff] at hxP
    have h0 : ((∑ i, c i • b i : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)) : H1 N H ℤ)
        (Additive.ofMul γ) = 0 := hxP γ hγ
    have h1 : ((p : ℤ) • ψ) (Additive.ofMul γ) = 0 := by
      rw [← hψ]
      exact h0
    have h2 : (p : ℤ) * ψ (Additive.ofMul γ) = 0 := h1
    exact (mul_eq_zero.mp h2).resolve_left (by exact_mod_cast NeZero.ne p)
  have hx : (∑ i, c i • b i : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)) =
      (p : ℤ) • (⟨ψ, hψP⟩ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)) :=
    Subtype.ext hψ
  funext i
  have h1 := congrFun (b.repr_sum_self c) i
  rw [hx] at h1
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  rw [Pi.zero_apply, ← hc i, ← h1, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

private theorem exists_apply_sub_smul_eq_natCast_smul (N : ℕ) (H : Subgroup (ZMod N)ˣ) {t : ℕ}
    (b : Module.Basis (Fin t) ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ))
    (T : H1 N H ℤ →+ H1 N H ℤ)
    (hT : ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      T.toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)
    {p : ℕ} [NeZero p] (m : Fin t → ZMod p) (nn : ℤ) (c : Fin t → ℤ) (hc : ∀ i, (c i : ZMod p) = m i)
    (hm : ((latticeMatrix N H b T hT).map (Int.cast : ℤ → ZMod p)).mulVec m = (nn : ZMod p) • m) :
    ∃ ψ : H1 N H ℤ,
      T ((∑ i, c i • b i : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)) : H1 N H ℤ) -
        nn • ((∑ i, c i • b i : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)) : H1 N H ℤ) =
          (p : ℤ) • ψ := by
  classical
  set x : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ) := ∑ i, c i • b i with hxdef
  have hx : ⇑(b.repr x) = c := b.repr_sum_self c
  have hTx : ⇑(b.repr ((T.toIntLinearMap.restrict hT) x)) = (latticeMatrix N H b T hT).mulVec c := by
    rw [← hx]
    exact (LinearMap.toMatrix_mulVec_repr b b (T.toIntLinearMap.restrict hT) x).symm

  have hdiv : ∀ i, ∃ d : ℤ, (latticeMatrix N H b T hT).mulVec c i - nn * c i = p * d := by
    intro i
    have hdvd : (p : ℤ) ∣ (latticeMatrix N H b T hT).mulVec c i - nn * c i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul]
      have h1 : (((latticeMatrix N H b T hT).mulVec c i : ℤ) : ZMod p) =
          ((latticeMatrix N H b T hT).map (Int.cast : ℤ → ZMod p)).mulVec m i := by
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul, hc]
      rw [h1, hm, Pi.smul_apply, smul_eq_mul, hc i, sub_self]
    exact hdvd
  choose d hd using hdiv
  refine ⟨((∑ i, d i • b i : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)) : H1 N H ℤ), ?_⟩
  have key : (T.toIntLinearMap.restrict hT) x - nn • x = (p : ℤ) • ∑ i, d i • b i := by
    apply b.repr.injective
    ext i
    simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hTx, hx,
      b.repr_sum_self]
    exact hd i
  have key' := congrArg Subtype.val key
  simpa only [Submodule.coe_sub, Submodule.coe_smul, LinearMap.coe_restrict_apply,
    AddMonoidHom.coe_toIntLinearMap] using key'

private theorem exists_integral_eigenclass_congr_of_complex_eigenclass
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (S : Finset ℕ) (n : ℕ → ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (φ : CohCarrier.H1 N H ℂ) (hφ0 : φ ≠ 0)
    (hφpar : φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N H) ℂ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ α : integralClosure ℤ ℂ, CohCarrier.heckeT N H ℓ ℂ φ = (α : ℂ) • φ ∧ α - (n ℓ : integralClosure ℤ ℂ) ∈ 𝔪)
    (hdia : ∀ σ : CongruenceSubgroup.Gamma0 N, ∃ (c : ℂ) (k : ℕ), c ^ p ^ k = 1 ∧ CohCarrier.diamondRaw N H ℂ σ φ = c • φ) :
    ∃ φ₀ : CohCarrier.H1 N H ℤ, (¬ ∃ ψ : CohCarrier.H1 N H ℤ, φ₀ = (p : ℤ) • ψ) ∧
      φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) ℤ ∧
      (∀ σ : CongruenceSubgroup.Gamma0 N, ∃ ψ : CohCarrier.H1 N H ℤ, CohCarrier.diamondRaw N H ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 N H ℤ, CohCarrier.heckeT N H ℓ ℤ φ₀ - n ℓ • φ₀ = (p : ℤ) • ψ) := by
  classical
  haveI : (GammaH N H).FiniteIndex := finiteIndex_gammaH N H
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨t, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (GammaH N H)
  obtain ⟨bC, hbC⟩ := hb ℂ
  set x : ↥(ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ) := ⟨φ, hφpar⟩ with hxdef

  have hv : (⇑(bC.repr x) : Fin t → ℂ) ≠ 0 := by
    intro h0
    apply hφ0
    have h1 : bC.repr x = 0 := DFunLike.coe_injective (h0.trans Finsupp.coe_zero.symm)
    have h2 : x = 0 := bC.repr.injective (h1.trans (map_zero bC.repr).symm)
    exact congrArg Subtype.val h2

  have hTc : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N},
      haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
      ∃ α : integralClosure ℤ ℂ, heckeT N H ℓ.1 ℂ φ = (α : ℂ) • φ ∧
        α - (n ℓ.1 : integralClosure ℤ ℂ) ∈ 𝔪 :=
    fun ℓ => hT ℓ.1 ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2
  choose αT hαT using hTc
  choose cD kD hcD hdD using hdia
  have hζ : ∀ σ : Gamma0 N, ∃ ζ : integralClosure ℤ ℂ, (ζ : ℂ) = cD σ ∧ ζ - 1 ∈ 𝔪 := fun σ =>
    exists_integralClosure_coe_eq_and_sub_one_mem_of_pow_prime_pow_eq_one p 𝔪 h𝔪 hp𝔪 (cD σ) (kD σ)
      (hcD σ)
  choose ζD hζc hζ1 using hζ

  have hTZ : ∀ (ℓ : ℕ) [NeZero ℓ], ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      (heckeT N H ℓ ℤ).toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ :=
    fun ℓ _ ψ hψ => heckeT_mem_parabolicHoms N H ℓ hψ
  have hDZ : ∀ σ : Gamma0 N, ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ,
      (diamondRaw N H ℤ σ).toIntLinearMap ψ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ :=
    fun σ ψ hψ => diamondRaw_mem_parabolicHoms N H σ hψ
  have hTCpar : ∀ (ℓ : ℕ) [NeZero ℓ], ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ,
      heckeTL N H ℂ ℓ ψ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ :=
    fun ℓ _ ψ hψ => heckeT_mem_parabolicHoms N H ℓ hψ
  have hDCpar : ∀ σ : Gamma0 N, ∀ ψ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ,
      diamondLin N H ℂ σ ψ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ :=
    fun σ ψ hψ => diamondRaw_mem_parabolicHoms N H σ hψ

  let A : ({ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N} ⊕ ↥(Gamma0 N)) → Matrix (Fin t) (Fin t) ℤ :=
    Sum.elim
      (fun ℓ => haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩;
        latticeMatrix N H b (heckeT N H ℓ.1 ℤ) (hTZ ℓ.1))
      (fun σ => latticeMatrix N H b (diamondRaw N H ℤ σ) (hDZ σ))
  let α : ({ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N} ⊕ ↥(Gamma0 N)) → integralClosure ℤ ℂ :=
    Sum.elim αT ζD
  let nn : ({ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N} ⊕ ↥(Gamma0 N)) → ℤ :=
    Sum.elim (fun ℓ => n ℓ.1) (fun _ => 1)
  have heig : ∀ i, ((A i).map (Int.cast : ℤ → ℂ)).mulVec ⇑(bC.repr x) = ((α i : ℂ) • ⇑(bC.repr x)) := by
    rintro (ℓ | σ)
    · haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
      exact map_latticeMatrix_mulVec_repr N H b bC hbC (heckeT N H ℓ.1 ℤ) (hTZ ℓ.1)
        (heckeTL N H ℂ ℓ.1) (hTCpar ℓ.1)
        (fun ψ => heckeT_comp_coeff N H ℓ.1 (Int.castAddHom ℂ) ψ) x (αT ℓ) (hαT ℓ).1
    · refine map_latticeMatrix_mulVec_repr N H b bC hbC (diamondRaw N H ℤ σ) (hDZ σ)
        (diamondLin N H ℂ σ) (hDCpar σ) (fun ψ => rfl) x (ζD σ) ?_
      show diamondRaw N H ℂ σ φ = (ζD σ : ℂ) • φ
      rw [hζc]
      exact hdD σ
  have hcong : ∀ i, α i - (nn i : integralClosure ℤ ℂ) ∈ 𝔪 := by
    rintro (ℓ | σ)
    · exact (hαT ℓ).2
    · show ζD σ - ((1 : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪
      rw [Int.cast_one]
      exact hζ1 σ

  obtain ⟨m, hm0, hm⟩ :=
    DeligneSerre.exists_modP_eigenvector_of_complex_eigenvector A h𝔪.isPrime hp𝔪 hv heig hcong

  let c : Fin t → ℤ := fun i => ((m i).val : ℤ)
  have hc : ∀ i, (c i : ZMod p) = m i := fun i => by
    show (((m i).val : ℤ) : ZMod p) = m i
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨((∑ i, c i • b i : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N H) ℤ)) : H1 N H ℤ),
    not_exists_eq_natCast_smul N H b m hm0 c hc, (∑ i, c i • b i).2, fun σ => ?_,
    fun ℓ hℓ hS hN => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_apply_sub_smul_eq_natCast_smul N H b (diamondRaw N H ℤ σ) (hDZ σ)
      m 1 c hc (hm (Sum.inr σ))
    refine ⟨ψ, ?_⟩
    simpa only [one_smul, one_zsmul] using hψ
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact exists_apply_sub_smul_eq_natCast_smul N H b (heckeT N H ℓ ℤ) (hTZ ℓ) m (n ℓ) c hc
      (hm (Sum.inl ⟨ℓ, hℓ, hS, hN⟩))

end LevelLowering

end

section

open scoped WeierstrassCurve.Affine in

private theorem torsion_card (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2 := by
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic := ⟨by simp [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, hΔ]⟩
  exact WeierstrassCurve.card_torsion_of_isAlgClosed_light (W.map (Int.castRingHom ℚ))
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

private theorem torsion_finite_level (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0) :
    GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p) := by
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic := ⟨by simp [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, hΔ]⟩
  exact WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel (W.map (Int.castRingHom ℚ)) p

private theorem two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)

namespace WeierstrassCurve p2m_export "WeierstrassCurve" "Affine map mk reduction IsIntegral Affine.Point map_Δ Δ baseChange j ModRepIsIrreducible card apOfModel IsGoodPrimeFor IsSemistableModel IsIntegralModelOf residualGaloisRepOf Affine.Point.galoisRepModuleEnd exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra card_torsion_of_isAlgClosed_light galoisRepModuleEnd_factorsThroughFiniteLevel residualGaloisRepOf_isIrreducible_iff residualGaloisRepOf_isOdd residualGaloisRepOf_restrict_index_two" end WeierstrassCurve
p2m_open_scoped "WeierstrassCurve" in

private theorem WeierstrassCurve.exists_residualGaloisRep_isAbsolutelyIrreducible_trace_eq_apOfModel
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k p) (ρbar : ResidualGaloisRep k),
      ρbar.IsAbsolutelyIrreducible ∧
      (p = 3 → ∀ (K : Type) [Field K] [Algebra k K]
        (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
          ∀ V : Submodule K (ρbar.baseChange K).V,
            (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤) ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.trace k ρbar.V (ρbar.ρ σ) = (W.apOfModel ℓ : k) := by
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic := ⟨by simp [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, hΔ]⟩
  refine ⟨ZMod p, inferInstance, inferInstance,
    (W.map (Int.castRingHom ℚ)).residualGaloisRepOf p (torsion_card W p hΔ) (torsion_finite_level W p hΔ),
    ?_, ?_, ?_⟩
  · exact ResidualGaloisRep.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd _ (two_ne_zero_zmod p hp2)
      ((WeierstrassCurve.residualGaloisRepOf_isIrreducible_iff _ p _ _).mpr hirr)
      (WeierstrassCurve.residualGaloisRepOf_isOdd _ p _ _)
  · intro _ K _ _ G hG V hV
    exact WeierstrassCurve.residualGaloisRepOf_restrict_index_two W p hp2 hΔ hW hirr (torsion_card W p hΔ)
      (torsion_finite_level W p hΔ) K G hG V hV
  · intro ℓ hℓ hgood hℓp A hA σ hσ
    have hmodel : W.IsIntegralModelOf (W.map (Int.castRingHom ℚ)) := ⟨1, one_smul _ _⟩
    exact (hmodel.galoisTrace_det_frobenius p ℓ Fact.out hℓ hℓp hgood A hA σ hσ).1
end

private theorem notMem_excluded_iff {W : WeierstrassCurve ℤ} (hΔ : W.Δ ≠ 0) {M p ℓ : ℕ} (hM : M ≠ 0)
    (hℓ : ℓ.Prime) :
    ℓ ∉ M.divisors ∪ {p} ∪ W.Δ.natAbs.primeFactors ↔ ¬ ℓ ∣ M ∧ ℓ ≠ p ∧ W.IsGoodPrimeFor ℓ := by
  constructor
  · intro h
    refine ⟨fun hℓM => h (Finset.mem_union_left _ (Finset.mem_union_left _ (Nat.mem_divisors.mpr ⟨hℓM, hM⟩))),
      fun hℓp => h (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr hℓp))),
      fun hdvd => h (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨hℓ, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr hΔ⟩))⟩
  · rintro ⟨hℓM, hℓp, hgood⟩ h
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hℓM (Nat.mem_divisors.mp h).1
      · exact hℓp (Finset.mem_singleton.mp h)
    · exact hgood (Int.natCast_dvd.mpr (Nat.mem_primeFactors.mp h).2.1)

private theorem mul_sub_mem_of_sub_one_mem {𝔪 : Ideal (integralClosure ℤ ℂ)} {ζ a : integralClosure ℤ ℂ}
    {n : ℤ} (hζ : ζ - 1 ∈ 𝔪) (ha : a - (n : integralClosure ℤ ℂ) ∈ 𝔪) :
    ζ * a - (n : integralClosure ℤ ℂ) ∈ 𝔪 := by
  have h : ζ * a - (n : integralClosure ℤ ℂ) = (ζ - 1) * a + (a - (n : integralClosure ℤ ℂ)) := by ring
  rw [h]
  exact 𝔪.add_mem (Ideal.mul_mem_right a 𝔪 hζ) ha

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) {M : ℕ} [NeZero M] {L : ℕ}
    (hLM : L ∣ M) {q : ℕ} (hqp : q ≠ p) (hq2 : L.factorization q = 2)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (𝔪 : Ideal (integralClosure ℤ ℂ))
    (hg : g.IsNewform) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪)
    [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηfin : HeckeCharacter.IsFiniteOrderHeckeChar ℚ η)
    (hηmod : HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel q))
    (hηp : ∀ u : ℤ_[q]ˣ, ∃ n : ℕ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
        (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
          (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) ^ p ^ n = 1)
    (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)))
    (hy0 : y ≠ 0)
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q 1)
      (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)))
    (hcent : ∀ u : ℤ_[q]ˣ, LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
      ((η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom
              (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) : ℂ) ^ 2) • y) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (L / q)) 2) (𝔪' : Ideal (integralClosure ℤ ℂ)),
      f.IsNormalizedEigenform ∧ 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪' := by

  have _ := hqp

  obtain ⟨-, hN0, hNM, hqN⟩ := LevelLowering.ne_zero_and_div_ne_zero_and_div_dvd_and_dvd_div hq2 hLM
  haveI : NeZero (L / q) := ⟨hN0⟩

  have hM0 : M ≠ 0 := NeZero.ne M
  have hS : ∀ ℓ : ℕ, ℓ.Prime →
      (ℓ ∉ M.divisors ∪ {p} ∪ W.Δ.natAbs.primeFactors ↔ ¬ ℓ ∣ M ∧ ℓ ≠ p ∧ W.IsGoodPrimeFor ℓ) :=
    fun ℓ hℓ => notMem_excluded_iff hΔ hM0 hℓ

  obtain ⟨φ, hφ0, hφpar, hφdia, hφT⟩ :=
    hg.isNormalizedEigenform.exists_H1_diamondRaw_eq_smul_heckeT_eq_smul_of_mem_fixedSubmodule_fnTwist
      q hq2 Φ hΦg η hηfin hηmod y hy hy0 hfix hcent

  have hdia : ∀ σ : CongruenceSubgroup.Gamma0 (L / q), ∃ (c : ℂ) (k : ℕ), c ^ p ^ k = 1 ∧
      CohCarrier.diamondRaw (L / q) ⊥ ℂ σ φ = c • φ := by
    intro σ
    obtain ⟨u, hu⟩ := LevelLowering.exists_units_coe_eq_lowerRight_of_dvd hqN σ
    obtain ⟨k, hk⟩ := LevelLowering.inv_sq_coe_apply_pow_prime_pow_eq_one p η hηp u
    exact ⟨_, k, hk, hφdia σ u hu⟩

  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ M.divisors ∪ {p} ∪ W.Δ.natAbs.primeFactors → ¬ ℓ ∣ L / q →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ α : integralClosure ℤ ℂ, CohCarrier.heckeT (L / q) ⊥ ℓ ℂ φ = (α : ℂ) • φ ∧
        α - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪 := by
    intro ℓ hℓ hℓS _
    obtain ⟨hℓM, hℓp, hgood⟩ := (hS ℓ hℓ).mp hℓS
    have hℓL : ¬ ℓ ∣ L := fun h => hℓM (dvd_trans h hLM)
    obtain ⟨ζ, hζ, hζ1⟩ :=
      LevelLowering.exists_integralClosure_coe_eq_apply_uniformizerIdele_and_sub_one_mem p hq2 η hηfin hηmod
        hηp 𝔪 h𝔪 hp𝔪 ℓ hℓ hℓL
    obtain ⟨a, ha, ha𝔪⟩ := hcong ℓ hℓ hgood hℓM hℓp
    refine ⟨ζ * a, ?_, mul_sub_mem_of_sub_one_mem hζ1 ha𝔪⟩
    rw [hφT ℓ hℓ hℓL, Subalgebra.coe_mul, hζ, ha]

  obtain ⟨φ₀, hφ₀, hφ₀par, hdia₀, hT₀⟩ :=
    LevelLowering.exists_integral_eigenclass_congr_of_complex_eigenclass p (L / q) ⊥
      (M.divisors ∪ {p} ∪ W.Δ.natAbs.primeFactors) W.apOfModel 𝔪 h𝔪 hp𝔪 φ hφ0 hφpar hT hdia

  obtain ⟨k, _, _, ρbar, hρirr, hρ3, hρtr⟩ :=
    WeierstrassCurve.exists_residualGaloisRep_isAbsolutelyIrreducible_trace_eq_apOfModel p hp2 W hΔ hW hirr
  have htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ M.divisors ∪ {p} ∪ W.Δ.natAbs.primeFactors → ¬ ℓ ∣ L / q →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (W.apOfModel ℓ : k) := by
    intro ℓ hℓ hℓS _ A hA σ hσ
    obtain ⟨-, hℓp, hgood⟩ := (hS ℓ hℓ).mp hℓS
    exact hρtr ℓ hℓ hgood hℓp A hA σ hσ

  obtain ⟨𝔪₀, h𝔪₀, hp𝔪₀, hT𝔪₀⟩ :=
    CohCarrier.exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible p hp2
      (L / q) ⊥ ((M.divisors ∪ {p} ∪ W.Δ.natAbs.primeFactors : Finset ℕ) : Set ℕ)
      (M.divisors ∪ {p} ∪ W.Δ.natAbs.primeFactors) W.apOfModel φ₀ hφ₀par hφ₀ hdia₀ hT₀ k ρbar hρirr hρ3 htr

  obtain ⟨f, 𝔪', hf, h𝔪', hp𝔪', hf𝔪'⟩ :=
    WeierstrassCurve.exists_isNormalizedEigenform_and_qCoeff_sub_apOfModel_mem_of_ideal_heckeAlgebra W p
      (L / q) ((M.divisors ∪ {p} ∪ W.Δ.natAbs.primeFactors : Finset ℕ) : Set ℕ) 𝔪₀ h𝔪₀ hp𝔪₀
      (fun ℓ hℓ hℓN hℓS => hT𝔪₀ ℓ hℓ hℓN hℓS (fun h => hℓS (Finset.mem_coe.mpr h)))
  refine ⟨f, 𝔪', hf, h𝔪', hp𝔪', fun ℓ hℓ hgood hℓM hℓp => ?_⟩
  exact hf𝔪' ℓ hℓ (fun h => hℓM (dvd_trans h hNM))
    (fun h => (hS ℓ hℓ).mpr ⟨hℓM, hℓp, hgood⟩ (Finset.mem_coe.mp h))

end S_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_mem_fixedSubmodule_fnTwist_of_isNewform_of_factorization_eq_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_isNormalizedEigenform_level_div_of_mem_fixedSubmodule_fnTwist_of_isNewform_of_factorization_eq_two (solution)
