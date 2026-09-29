-- Prove2me | solution 1 for WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e13d0bbf-54fd-59c4-8dd0-6e8d1e4e209d

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_IharaIota
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two
import Theorems.Thm_HeckeEis_exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two
import Theorems.Thm_HeckeEis_exists_retraction_binaryFormEval
import Theorems.Thm_HeckeEis_binaryFormEval_binaryFormRepSL
import Theorems.Thm_HeckeEis_binaryFormEval_binaryFormAlphaAdj
import Theorems.Thm_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction
import Theorems.Thm_HeckeEis_exists_coeffH1par_projLineRepSL_equiv_parabolicHoms
import Theorems.Thm_HeckeEis_postcomp_heckeOperatorHom
import Theorems.Thm_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
import Theorems.Thm_ModularCurve_Period_exists_ideal_heckeAlgebra_two_of_int_modp_eigenclass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "HeckeEis.coe_linePow ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Finset CuspForm CongruenceSubgroup
open scoped MatrixGroups

namespace P2mWeightTrade

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_eq_one_add_pow_succ_smul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : Matrix ι ι ℤ} (hM : M ^ p = 1) {k : ℕ} (hk : 1 ≤ k)
    (A : Matrix ι ι ℤ) (hA : M = 1 + (p : ℤ) ^ k • A) :
    ∃ A' : Matrix ι ι ℤ, M = 1 + (p : ℤ) ^ (k + 1) • A' := by
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · have := hp.two_le; omega
  have hcomm : Commute ((p : ℤ) ^ k • A) 1 := Commute.one_right _

  have hexp : ((p : ℤ) ^ k • A + 1) ^ p
      = ∑ m ∈ range (p + 1), ((p.choose m : ℤ) * (p : ℤ) ^ (k * m)) • A ^ m := by
    rw [hcomm.add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [one_pow, mul_one, ← nsmul_eq_mul', smul_pow, ← pow_mul, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]

  have hdiv : ∀ m ∈ range (p - 1), ∃ c : ℤ, ((p.choose (m + 2) : ℤ)) * (p : ℤ) ^ (k * (m + 2))
      = (p : ℤ) ^ (k + 2) * c := by
    intro m hm
    rw [Finset.mem_range] at hm
    by_cases hlt : m + 2 < p
    · obtain ⟨d, hd⟩ := hp.dvd_choose_self (by omega) hlt
      refine ⟨(d : ℤ) * (p : ℤ) ^ (k * (m + 2) - (k + 1)), ?_⟩
      have hle : k + 1 ≤ k * (m + 2) := by nlinarith
      rw [hd]
      push_cast
      have : (p : ℤ) ^ (k * (m + 2)) = (p : ℤ) ^ (k + 1) * (p : ℤ) ^ (k * (m + 2) - (k + 1)) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring
    · have hm2 : m + 2 = p := by omega
      refine ⟨(p.choose (m + 2) : ℤ) * (p : ℤ) ^ (k * (m + 2) - (k + 2)), ?_⟩
      have hle : k + 2 ≤ k * (m + 2) := by rw [hm2]; nlinarith
      have : (p : ℤ) ^ (k * (m + 2)) = (p : ℤ) ^ (k + 2) * (p : ℤ) ^ (k * (m + 2) - (k + 2)) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring
  choose c hc using hdiv
  set B : Matrix ι ι ℤ := ∑ m ∈ (range (p - 1)).attach, c m.1 m.2 • A ^ (m.1 + 2) with hB

  have htail : ∑ m ∈ range (p - 1), ((p.choose (m + 2) : ℤ) * (p : ℤ) ^ (k * (m + 2))) • A ^ (m + 2)
      = (p : ℤ) ^ (k + 2) • B := by
    rw [hB, Finset.smul_sum, ← Finset.sum_attach (range (p - 1))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hc m.1 m.2, smul_smul]
  have hsum : ((p : ℤ) ^ k • A + 1) ^ p = 1 + (p : ℤ) ^ (k + 1) • A + (p : ℤ) ^ (k + 2) • B := by
    rw [hexp]
    have hp1 : p + 1 = (p - 1) + 1 + 1 := by omega
    rw [hp1, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_zero, one_smul, zero_add, mul_one,
      Nat.choose_one_right, pow_one]
    rw [htail, ← pow_succ']
    abel
  have hM' : ((p : ℤ) ^ k • A + 1) ^ p = 1 := by rw [add_comm, ← hA]; exact hM
  rw [hM'] at hsum

  have hzero : (p : ℤ) ^ (k + 1) • (A + (p : ℤ) • B) = 0 := by
    have h1 : (p : ℤ) ^ (k + 1) • A + (p : ℤ) ^ (k + 2) • B = 0 := by
      have := hsum; rw [add_assoc] at this
      exact (add_eq_left.mp this.symm)
    rw [smul_add, smul_smul, ← pow_succ]
    exact h1
  have hAB : A + (p : ℤ) • B = 0 := by
    ext i j
    have := congrFun (congrFun hzero i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, mul_eq_zero, pow_eq_zero_iff',
      Int.natCast_eq_zero, ne_eq] at this
    rcases this with ⟨h0, -⟩ | h
    · exact absurd h0 hp.ne_zero
    · simpa using h
  refine ⟨-B, ?_⟩
  rw [hA, eq_neg_of_add_eq_zero_left hAB, smul_neg, smul_smul, ← pow_succ, smul_neg]

theorem eq_one_of_pow_prime_eq_one_of_modEq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {M : Matrix ι ι ℤ} (hM : M ^ p = 1) (hmod : ∀ i j, (p : ℤ) ∣ (M - 1) i j) : M = 1 := by

  have hall : ∀ k : ℕ, 1 ≤ k → ∃ A : Matrix ι ι ℤ, M = 1 + (p : ℤ) ^ k • A := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        choose a ha using hmod
        refine ⟨Matrix.of fun i j => a i j, ?_⟩
        ext i j
        have := ha i j
        simp only [Matrix.sub_apply] at this
        simp only [zero_add, pow_one, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
        linarith
      · obtain ⟨A, hA⟩ := ih hkpos
        exact exists_eq_one_add_pow_succ_smul hp hp2 hM hkpos A hA
  ext i j
  have hdvd : ∀ k : ℕ, 1 ≤ k → (p : ℤ) ^ k ∣ (M - 1) i j := by
    intro k hk
    obtain ⟨A, hA⟩ := hall k hk
    refine ⟨A i j, ?_⟩
    rw [hA]; simp only [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]
  suffices h : (M - 1) i j = 0 by
    have := h; rw [Matrix.sub_apply, sub_eq_zero] at this; exact this
  set x := (M - 1) i j
  refine Int.eq_zero_of_abs_lt_dvd (hdvd (x.natAbs + 1) (by omega)) ?_
  have h1 : (x.natAbs : ℤ) < (p : ℤ) ^ (x.natAbs + 1) := by
    have := Nat.lt_pow_self (n := x.natAbs + 1) hp.one_lt
    exact_mod_cast (show x.natAbs < p ^ (x.natAbs + 1) by omega)
  rw [Int.abs_eq_natAbs]; exact h1

theorem eq_one_of_pow_prime_pow_eq_one_of_modEq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ℕ) {M : Matrix ι ι ℤ} (hM : M ^ (p ^ e) = 1) (hmod : ∀ i j, (p : ℤ) ∣ (M - 1) i j) : M = 1 := by
  induction e generalizing M with
  | zero => simpa using hM
  | succ e ih =>
    have hMp : ∀ i j, (p : ℤ) ∣ (M ^ p - 1) i j := by

      choose a ha using hmod
      set A : Matrix ι ι ℤ := Matrix.of fun i j => a i j
      have hA : M = 1 + (p : ℤ) • A := by
        ext i j; have := ha i j
        simp only [Matrix.sub_apply] at this
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, A]; linarith
      have hcomm : Commute ((p : ℤ) • A) 1 := Commute.one_right _
      have hexp : M ^ p = 1 + (p : ℤ) • ∑ m ∈ range p, ((p : ℤ) ^ m * (p.choose (m + 1) : ℤ)) • A ^ (m + 1) := by
        rw [hA, add_comm, hcomm.add_pow, Finset.sum_range_succ']
        simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one]
        rw [add_comm, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_pow, ← nsmul_eq_mul', smul_smul, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, pow_succ]
        congr 1; ring
      intro i j
      refine ⟨(∑ m ∈ range p, ((p : ℤ) ^ m * (p.choose (m + 1) : ℤ)) • A ^ (m + 1)) i j, ?_⟩
      rw [hexp]; simp only [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]
    have h1 : M ^ p = 1 := by
      refine ih ?_ hMp
      rw [← pow_mul, ← pow_succ']; exact hM
    exact eq_one_of_pow_prime_eq_one_of_modEq hp hp2 h1 hmod

theorem sum_pow_zmod_eq (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : j ≤ p - 1) :
    ∑ t : ZMod p, t ^ j = if j = p - 1 then -1 else 0 := by
  have hp : p.Prime := Fact.out
  split_ifs with h
  · subst h
    have : ∀ t : ZMod p, t ^ (p - 1) = if t = 0 then 0 else 1 := by
      intro t
      split_ifs with ht
      · rw [ht, zero_pow]; have := hp.two_le; omega
      · exact ZMod.pow_card_sub_one_eq_one ht
    simp_rw [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (Finset.univ.filter fun t : ZMod p => ¬ t = 0).card = p - 1 := by
      rw [Finset.filter_not, Finset.card_univ_diff, ZMod.card]
      congr 1
      rw [Finset.card_eq_one]
      exact ⟨0, by ext; simp⟩
    rw [hcard, Nat.cast_sub hp.one_lt.le, Nat.cast_one, ZMod.natCast_self, zero_sub]
  · have hlt : j < Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) j hlt

theorem sum_eval_one_cast_eq_neg_eval (p : ℕ) [Fact p.Prime] (K : Type*) [CommRing K] [CharP K p]
    {F : MvPolynomial (Fin 2) K} (hF : F ∈ HeckeEis.BinaryForm K (p - 1)) :
    ∑ t : ZMod p, MvPolynomial.eval ![(1 : K), ZMod.castHom (dvd_refl p) K t] F
      = - MvPolynomial.eval ![(0 : K), 1] F := by
  have hp : p.Prime := Fact.out
  rw [HeckeEis.BinaryForm, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨d, hd, rfl⟩ := hG
    simp only [Set.mem_setOf_eq, Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    change ∑ t, MvPolynomial.eval _ (MvPolynomial.monomial d (1 : K)) = - MvPolynomial.eval _ (MvPolynomial.monomial d 1)
    simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_pow, one_mul]
    have hj : d 1 ≤ p - 1 := by omega
    simp_rw [← map_pow]
    rw [← map_sum, sum_pow_zmod_eq p (d 1) hj]
    by_cases h1 : d 1 = p - 1
    · have h0 : d 0 = 0 := by omega
      rw [if_pos h1, h0, pow_zero, map_neg, map_one, one_mul]
    · have h0 : d 0 ≠ 0 := by omega
      rw [if_neg h1, map_zero, zero_pow h0, zero_mul, neg_zero]
  | zero => simp
  | add G H _ _ hG hH =>
    simp only [map_add, Finset.sum_add_distrib, hG, hH, neg_add]
  | smul c G _ hG =>
    have h1 : ∀ x : Fin 2 → K, MvPolynomial.eval x (c • G) = c * MvPolynomial.eval x G :=
      fun x => MvPolynomial.smul_eval x G c
    change ∑ t, MvPolynomial.eval _ (c • G) = -MvPolynomial.eval _ (c • G)
    rw [h1, Finset.sum_congr rfl fun t _ => h1 _, ← Finset.mul_sum, hG, mul_neg]

theorem eval_binarySubst (K : Type*) [CommRing K] (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → K)
    (F : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval v (HeckeEis.binarySubst K M F)
      = MvPolynomial.eval (Matrix.vecMul v (M.map (Int.castRingHom K))) F := by
  rw [HeckeEis.binarySubst, MvPolynomial.aeval_eq_bind₁]
  change MvPolynomial.eval₂Hom (RingHom.id K) v (MvPolynomial.bind₁ _ F) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun j => MvPolynomial.eval v (∑ i : Fin 2, MvPolynomial.C ((M i j : ℤ) : K) *
    MvPolynomial.X i)) F = _
  congr 2
  funext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

section Cocycle
variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

theorem cocycle_one (ρ : Representation K G V) {z : G → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one] at h
  simpa using h

theorem cocycle_pow (ρ : Representation K G V) {z : G → V} (hz : z ∈ HeckeEis.coeffCocycles ρ) (g : G) (m : ℕ) :
    z (g ^ m) = ∑ i ∈ range m, (ρ g ^ i) (z g) := by
  induction m with
  | zero => rw [pow_zero, Finset.sum_range_zero]; exact cocycle_one ρ hz
  | succ m ih => rw [pow_succ, hz, ih, map_pow, Finset.sum_range_succ]

end Cocycle

section UT
variable {R : Type*} [CommRing R]

theorem pow_apply_of_apply_one_zero_eq_zero (B : Matrix (Fin 2) (Fin 2) R) (hB : B 1 0 = 0) (n : ℕ) :
    (B ^ n) 1 0 = 0 ∧ (B ^ n) 0 0 = B 0 0 ^ n ∧ (B ^ n) 1 1 = B 1 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h10, h00, h11⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, hB, zero_mul, mul_zero, add_zero]
    · rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h00, hB, mul_zero, add_zero, ← pow_succ]
    · rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, zero_mul, zero_add, ← pow_succ]

theorem pow_apply_zero_one_of_unipotent (B : Matrix (Fin 2) (Fin 2) R) (hB : B 1 0 = 0) (h00 : B 0 0 = 1)
    (h11 : B 1 1 = 1) (n : ℕ) : (B ^ n) 0 1 = n * B 0 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := pow_apply_of_apply_one_zero_eq_zero B hB n
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, ih, h.2.1, h00, h11, one_pow, one_mul, mul_one]
    push_cast; ring

theorem vecMul_zero_one_pow (B : Matrix (Fin 2) (Fin 2) R) (hB : B 1 0 = 0) (n : ℕ) :
    Matrix.vecMul ![(0 : R), 1] (B ^ n) = (B 1 1 ^ n) • ![(0 : R), 1] := by
  have h := pow_apply_of_apply_one_zero_eq_zero B hB n
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h.1, h.2.2]

theorem vecMul_one_zero_pow_of_unipotent (B : Matrix (Fin 2) (Fin 2) R) (hB : B 1 0 = 0) (h00 : B 0 0 = 1)
    (h11 : B 1 1 = 1) (n : ℕ) :
    Matrix.vecMul ![(1 : R), 0] (B ^ n) = ![(1 : R), n * B 0 1] := by
  have h := pow_apply_of_apply_one_zero_eq_zero B hB n
  have h' := pow_apply_zero_one_of_unipotent B hB h00 h11 n
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h.2.1, h', h00]

end UT

theorem sum_range_natCast_eq_sum_zmod (p : ℕ) [NeZero p] {M : Type*} [AddCommMonoid M] (h : ZMod p → M) :
    ∑ i ∈ range p, h (i : ZMod p) = ∑ u : ZMod p, h u := by
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun u => u.val) (fun _ _ => Finset.mem_univ _)
    (fun u _ => Finset.mem_range.mpr (ZMod.val_lt u)) (fun i hi => ?_) (fun u _ => ?_) (fun _ _ => rfl)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
  · exact ZMod.natCast_zmod_val u

section Core

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] {N : ℕ}

local notation "redK" M => Matrix.map (M : Matrix (Fin 2) (Fin 2) ℤ) (Int.castRingHom K)

omit [Fact p.Prime] [CharP K p] in
theorem eval_rho_pow_apply (g : Gamma0 N) (F : ↥(HeckeEis.BinaryForm K (p - 1))) (v : Fin 2 → K) (i : ℕ) :
    MvPolynomial.eval v
        ((((((HeckeEis.binaryFormRepSL K (p - 1)).comp (Gamma0 N).subtype) g) ^ i) F :
          ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K)
      = MvPolynomial.eval (Matrix.vecMul v ((redK ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ i)) F := by
  rw [← map_pow]
  change MvPolynomial.eval v (((HeckeEis.binaryFormRepSL K (p - 1)) ((g ^ i : Gamma0 N) : SL(2, ℤ)) F :
    ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K) = _
  rw [HeckeEis.binaryFormRepSL_apply_coe, eval_binarySubst, Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.map_pow]

theorem cast_apply_one_one_pow_eq_one (g : SL(2, ℤ)) (hpg : (p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : K) ^ (p - 1) = 1 := by
  have hp : p.Prime := Fact.out
  have hdet := Matrix.det_fin_two (g : Matrix (Fin 2) (Fin 2) ℤ)
  rw [g.det_coe] at hdet

  have hd0 : (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hc0 : (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpg
    have := congrArg (fun x : ℤ => (x : ZMod p)) hdet
    simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, h0, hc0, mul_zero, sub_zero] at this
    exact one_ne_zero this
  have h1 : (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hd0
  have := congrArg (ZMod.castHom (dvd_refl p) K) h1
  rwa [map_pow, map_one, map_intCast] at this

theorem intCast_eq_one_of_pow_prime_pow_eq_one (a : ℤ) (e : ℕ) (h : ((a : K)) ^ (p ^ e) = 1) : (a : K) = 1 := by
  have hfrob : ∀ n : ℕ, ((a : ZMod p)) ^ (p ^ n) = (a : ZMod p) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  have := congrArg (ZMod.castHom (dvd_refl p) K) (hfrob e)
  rw [map_pow, map_intCast] at this
  rw [← this, h]

theorem eval_zero_one_eq_zero_of_pow_prime_pow (hp2 : p ≠ 2)
    (z : Gamma0 N → ↥(HeckeEis.BinaryForm K (p - 1)))
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL K (p - 1)).comp (Gamma0 N).subtype))
    (δ : Gamma0 N) (e : ℕ) (hδ : δ ^ (p ^ e) = 1)
    (hpδ : (p : ℤ) ∣ ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    MvPolynomial.eval ![(0 : K), 1] ((z δ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K)
      = 0 := by
  have hp : p.Prime := Fact.out
  set ρ := (HeckeEis.binaryFormRepSL K (p - 1)).comp (Gamma0 N).subtype with hρ
  set D : Matrix (Fin 2) (Fin 2) ℤ := ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hD
  set B : Matrix (Fin 2) (Fin 2) K := D.map (Int.castRingHom K) with hB
  have hB10 : B 1 0 = 0 := by
    rw [hB, Matrix.map_apply, eq_intCast]; exact (CharP.intCast_eq_zero_iff K p _).mpr hpδ
  have hBpow : B ^ (p ^ e) = 1 := by
    rw [hB, ← Matrix.map_pow, hD, ← Matrix.SpecialLinearGroup.coe_pow, ← Subgroup.coe_pow, hδ]
    simp [Matrix.map_one]
  have hut := pow_apply_of_apply_one_zero_eq_zero B hB10 (p ^ e)
  have hB00 : B 0 0 = 1 := by
    have h : B 0 0 ^ (p ^ e) = 1 := by rw [← hut.2.1, hBpow]; simp
    rw [hB, Matrix.map_apply, eq_intCast] at h ⊢
    exact intCast_eq_one_of_pow_prime_pow_eq_one p K _ e h
  have hB11 : B 1 1 = 1 := by
    have h : B 1 1 ^ (p ^ e) = 1 := by rw [← hut.2.2, hBpow]; simp
    rw [hB, Matrix.map_apply, eq_intCast] at h ⊢
    exact intCast_eq_one_of_pow_prime_pow_eq_one p K _ e h

  have htors : ∀ (M : Gamma0 N) (f : ℕ), M ^ (p ^ f) = 1 →
      (((M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom K) = 1) → M = 1 := by
    intro M f hMf hM1
    have hmod : ∀ i j, (p : ℤ) ∣ (((M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) i j := by
      intro i j
      have hij := congrFun (congrFun hM1 i) j
      rw [Matrix.map_apply, eq_intCast] at hij
      rw [← CharP.intCast_eq_zero_iff K p, Matrix.sub_apply, Int.cast_sub, hij]
      fin_cases i <;> fin_cases j <;> simp
    have hMpow : ((M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ^ (p ^ f) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, ← Subgroup.coe_pow, hMf]; rfl
    have h1 := eq_one_of_pow_prime_pow_eq_one_of_modEq hp hp2 f hMpow hmod
    exact Subtype.ext (Subtype.ext (by rw [h1]; rfl))
  by_cases hb : B 0 1 = 0
  ·
    have hB1 : B = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hB00, hb, hB10, hB11]
    have hδ1 : δ = 1 := htors δ e hδ (by rw [← hB]; exact hB1)
    rw [hδ1, cocycle_one ρ hz]; simp
  ·
    have hδp : δ ^ p = 1 := by
      refine htors (δ ^ p) e ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, hδ, one_pow]
      · rw [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow, Matrix.map_pow, ← hD, ← hB]
        have hut' := pow_apply_of_apply_one_zero_eq_zero B hB10 p
        have h01 := pow_apply_zero_one_of_unipotent B hB10 hB00 hB11 p
        ext i j; fin_cases i <;> fin_cases j
        · simp [hut'.2.1, hB00]
        · simp [h01]
        · simp [hut'.1]
        · simp [hut'.2.2, hB11]

    have hsum : ∑ i ∈ range p, MvPolynomial.eval ![(1 : K), (i : K) * B 0 1]
        ((z δ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K) = 0 := by
      have h0 : z (δ ^ p) = 0 := by rw [hδp, cocycle_one ρ hz]
      rw [cocycle_pow ρ hz δ p] at h0
      have h1 := congrArg (fun F : ↥(HeckeEis.BinaryForm K (p - 1)) =>
        MvPolynomial.eval ![(1 : K), 0] (F : MvPolynomial (Fin 2) K)) h0
      simp only [AddSubmonoidClass.coe_finsetSum, map_sum, ZeroMemClass.coe_zero, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hρ, eval_rho_pow_apply, ← hD, ← hB, vecMul_one_zero_pow_of_unipotent B hB10 hB00 hB11 i]

    set b₀ : ZMod p := ((D 0 1 : ℤ) : ZMod p) with hb₀
    have hbcast : B 0 1 = ZMod.castHom (dvd_refl p) K b₀ := by
      rw [hB, Matrix.map_apply, eq_intCast, hb₀, map_intCast]
    have hb₀ne : b₀ ≠ 0 := by
      intro h0; apply hb; rw [hbcast, h0, map_zero]
    have hsum' : ∑ t : ZMod p, MvPolynomial.eval ![(1 : K), ZMod.castHom (dvd_refl p) K t]
        ((z δ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K) = 0 := by
      rw [← Fintype.sum_equiv (Equiv.mulRight₀ b₀ hb₀ne)
        (fun u => MvPolynomial.eval ![(1 : K), ZMod.castHom (dvd_refl p) K (u * b₀)]
          ((z δ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K)) _ (fun _ => rfl)]
      haveI : NeZero p := ⟨hp.ne_zero⟩
      rw [← sum_range_natCast_eq_sum_zmod p (fun u => MvPolynomial.eval
        ![(1 : K), ZMod.castHom (dvd_refl p) K (u * b₀)]
          ((z δ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K)), ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_natCast, hbcast]
    rw [sum_eval_one_cast_eq_neg_eval p K (z δ).2] at hsum'
    exact neg_eq_zero.mp hsum'

theorem eval_zero_one_eq_zero_of_isOfFinOrder (hp2 : p ≠ 2)
    (z : Gamma0 N → ↥(HeckeEis.BinaryForm K (p - 1)))
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL K (p - 1)).comp (Gamma0 N).subtype))
    (γ : Gamma0 N) (hγ : IsOfFinOrder γ) (hpγ : (p : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    MvPolynomial.eval ![(0 : K), 1] ((z γ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K)
      = 0 := by
  have hp : p.Prime := Fact.out
  set ρ := (HeckeEis.binaryFormRepSL K (p - 1)).comp (Gamma0 N).subtype with hρ
  obtain ⟨e, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (hγ.orderOf_pos).ne' p hp.one_lt.ne'

  have hγm : (γ ^ m') ^ (p ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hmeq]; exact pow_orderOf_eq_one γ
  have hmem : (γ : SL(2, ℤ)) ∈ Gamma0 p := by
    rw [Gamma0_mem]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpγ
  have hpγm : (p : ℤ) ∣ (((γ ^ m' : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h : ((γ : SL(2, ℤ)) ^ m') ∈ Gamma0 p := Subgroup.pow_mem _ hmem m'
    rw [Gamma0_mem] at h
    rw [Subgroup.coe_pow]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h
  have hvan := eval_zero_one_eq_zero_of_pow_prime_pow p K hp2 z hz (γ ^ m') e hγm hpγm

  set D : Matrix (Fin 2) (Fin 2) ℤ := ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hD
  set B : Matrix (Fin 2) (Fin 2) K := D.map (Int.castRingHom K) with hB
  have hB10 : B 1 0 = 0 := by
    rw [hB, Matrix.map_apply, eq_intCast]; exact (CharP.intCast_eq_zero_iff K p _).mpr hpγ
  have hd : B 1 1 ^ (p - 1) = 1 := by
    rw [hB, Matrix.map_apply, eq_intCast]; exact cast_apply_one_one_pow_eq_one p K (γ : SL(2, ℤ)) hpγ
  have hhom : ((z γ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K).IsHomogeneous (p - 1) :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp (z γ).2
  have hkey : MvPolynomial.eval ![(0 : K), 1]
      ((z (γ ^ m') : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K)
      = (m' : K) * MvPolynomial.eval ![(0 : K), 1]
        ((z γ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K) := by
    rw [cocycle_pow ρ hz γ m']
    simp only [AddSubmonoidClass.coe_finsetSum, map_sum]
    have : ∀ i ∈ range m', MvPolynomial.eval ![(0 : K), 1]
        ((((ρ γ) ^ i) (z γ) : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K)
        = MvPolynomial.eval ![(0 : K), 1] ((z γ : ↥(HeckeEis.BinaryForm K (p - 1))) : MvPolynomial (Fin 2) K) := by
      intro i _
      rw [hρ, eval_rho_pow_apply, ← hD, ← hB, vecMul_zero_one_pow B hB10 i,
        HeckeEis.eval_smul_of_isHomogeneous hhom, ← pow_mul, mul_comm i, pow_mul, hd, one_pow, one_mul]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hkey] at hvan
  have hm'K : (m' : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]; exact hm'
  exact (mul_eq_zero.mp hvan).resolve_left hm'K

end Core

section Arm

set_option maxHeartbeats 6400000 in
theorem weight_succ_arm (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (hS₀N : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S₀)
    (n : ℕ) (hn : n = p - 1)
    (𝔪ₖ : Ideal (heckeAlgebra N' ((n : ℤ) + 2) S₀)) (h𝔪ₖ : 𝔪ₖ.IsMaximal)
    (hp𝔪ₖ : (p : heckeAlgebra N' ((n : ℤ) + 2) S₀) ∈ 𝔪ₖ)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        heckeAlgebra.T hℓ hℓN hℓS -
          ((W.apOfModel ℓ : ℤ) : heckeAlgebra N' ((n : ℤ) + 2) S₀) ∈ 𝔪ₖ) :
    ∃ 𝔪₂ : Ideal (heckeAlgebra (N' * p) 2 S₀), 𝔪₂.IsMaximal ∧
      (p : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N' * p),
        W.IsGoodPrimeFor ℓ →
          heckeAlgebra.T hℓ hℓN hℓS -
            ((W.apOfModel ℓ : ℤ) : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ := by
  subst hn
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set ρS : Representation (ZMod p) (Gamma0 N') ↥(HeckeEis.BinaryForm (ZMod p) (p - 1)) :=
    (HeckeEis.binaryFormRepSL (ZMod p) (p - 1)).comp (Gamma0 N').subtype with hρS
  set ρP : Representation (ZMod p) (Gamma0 N') (ModularCurve.ProjectiveLine (ZMod p) → (ZMod p)) :=
    (HeckeEis.projLineRepSL p (ZMod p)).comp (Gamma0 N').subtype with hρP

  obtain ⟨x, hx0, hxeig⟩ :=
    HeckeEis.exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two N' (p - 1) S₀
      hS₀N p hp2 hpN' (Nat.sub_lt hp.pos Nat.one_pos) (fun ℓ => W.IsGoodPrimeFor ℓ)
      (fun ℓ => W.apOfModel ℓ) 𝔪ₖ h𝔪ₖ hp𝔪ₖ hocc (ZMod p)

  obtain ⟨r, hri, hrρ, hra⟩ := HeckeEis.exists_retraction_binaryFormEval p (ZMod p)
  have hi : ∀ g : Gamma0 N', HeckeEis.binaryFormEval p (ZMod p) ∘ₗ ρS g = ρP g ∘ₗ HeckeEis.binaryFormEval p (ZMod p) :=
    fun g => HeckeEis.binaryFormEval_binaryFormRepSL p (ZMod p) (g : SL(2, ℤ))
  have hr : ∀ g : Gamma0 N', r ∘ₗ ρP g = ρS g ∘ₗ r := fun g => hrρ (g : SL(2, ℤ))
  obtain ⟨I, R, hRI, hIformula, -, hIhecke⟩ :=
    HeckeEis.exists_coeffH1par_map_of_equivariant_retraction N' (ZMod p) ρS ρP
      (HeckeEis.binaryFormEval p (ZMod p)) r hi hr hri

  have hcop : Nat.Coprime p N' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN'
  obtain ⟨Sh, hShformula, hShhecke, -⟩ :=
    HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms N' p hcop (ZMod p)
  set φ : ↥(ModularCurve.Period.parabolicHoms (ZMod p) (Gamma0 (N' * p)) (ZMod p)) := Sh (I x) with hφ
  have hφ0 : φ ≠ 0 := by
    intro h
    apply hx0
    have hIx : I x = 0 := (LinearEquiv.map_eq_zero_iff Sh).mp h
    have hRIx : R (I x) = x := by
      have := LinearMap.congr_fun hRI x
      simpa using this
    rw [← hRIx, hIx, map_zero]
  have hφeig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      HeckeEis.heckeOperatorHom (N' * p) ℓ (ZMod p) (φ : Additive (Gamma0 (N' * p)) →+ (ZMod p))
        = (((W.apOfModel ℓ : ℤ) : (ZMod p)) • φ : ↥(ModularCurve.Period.parabolicHoms (ZMod p) (Gamma0 (N' * p)) (ZMod p))) := by
    intro ℓ hℓ hℓS hℓN hgood
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hS₀p)
    have hcopℓ : Nat.Coprime ℓ (N' * p) :=
      Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)
        ((Nat.coprime_primes hℓ hp).mpr hℓp)
    have hpℓ : p.Coprime ℓ := (Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp)
    obtain ⟨T', hT'ind, hT'transport⟩ := hShhecke ℓ hcopℓ
    obtain ⟨T, hTind, hTx⟩ := hxeig ℓ hℓ hℓS hℓN hgood
    have hcomm : T' ∘ₗ I = I ∘ₗ T :=
      hIhecke ℓ (HeckeEis.binaryFormAlphaAdj (ZMod p) (p - 1) ℓ) (HeckeEis.projLineAlphaAdj p (ZMod p) ℓ)
        (HeckeEis.binaryFormEval_binaryFormAlphaAdj p (ZMod p) ℓ hpℓ) T T' hTind hT'ind
    have h1 : T' (I x) = I (T x) := LinearMap.congr_fun hcomm x
    rw [← hT'transport (I x), h1, hTx, map_smul, map_smul]
  have hφtors : ∀ γ : Gamma0 (N' * p), IsOfFinOrder γ →
      (φ : Additive (Gamma0 (N' * p)) →+ (ZMod p)) (Additive.ofMul γ) = 0 := by
    intro γ hγ
    obtain ⟨zx, hzx⟩ := HeckeEis.coeffH1parMk_surjective ρS x
    obtain ⟨z₁, hz₁, hIz⟩ := hIformula zx
    rw [hφ, ← hzx, hIz, hShformula z₁ γ, hz₁]
    change HeckeEis.binaryFormEval p (ZMod p) ((zx : Gamma0 N' → ↥(HeckeEis.BinaryForm (ZMod p) (p - 1))) (Ihara.ι₀ N' p γ))
      (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧) = 0
    rw [HeckeEis.binaryFormEval_mk, HeckeEis.evalRow]
    have hvec : (![ZMod.castHom (dvd_refl p) (ZMod p) (0 : ZMod p), ZMod.castHom (dvd_refl p) (ZMod p) (1 : ZMod p)] :
        Fin 2 → (ZMod p)) = ![(0 : (ZMod p)), 1] := by
      rw [map_zero, map_one]
    change MvPolynomial.eval ![ZMod.castHom (dvd_refl p) (ZMod p) (0 : ZMod p), ZMod.castHom (dvd_refl p) (ZMod p) (1 : ZMod p)]
      (((zx : Gamma0 N' → ↥(HeckeEis.BinaryForm (ZMod p) (p - 1))) (Ihara.ι₀ N' p γ) :
        ↥(HeckeEis.BinaryForm (ZMod p) (p - 1))) : MvPolynomial (Fin 2) (ZMod p)) = 0
    rw [hvec]
    exact eval_zero_one_eq_zero_of_isOfFinOrder p (ZMod p) hp2 (zx : Gamma0 N' → ↥(HeckeEis.BinaryForm (ZMod p) (p - 1)))
      (HeckeEis.coeffParabolicCocycles_le_coeffCocycles ρS zx.2) (Ihara.ι₀ N' p γ)
      ((Ihara.ι₀ N' p).isOfFinOrder hγ) (Ihara.q_dvd_entry N' p γ)

  obtain ⟨xint, hxint⟩ :=
    ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
      (Gamma0 (N' * p)) p φ hφtors
  have hS' : ∀ q : ℕ, q.Prime → q ∣ N' * p → q ∈ S₀ := by
    intro q hq hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · exact hS₀N q hq h
    · rwa [(Nat.prime_dvd_prime_iff_eq hq hp).mp h]
  have hx' : (Int.castAddHom (ZMod p)).comp (xint : Additive (Gamma0 (N' * p)) →+ ℤ) ≠ 0 := by
    rw [hxint]
    exact fun h => hφ0 (Subtype.ext h)
  have heig' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ N' * p → W.IsGoodPrimeFor ℓ →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      (Int.castAddHom (ZMod p)).comp
          (HeckeEis.heckeOperatorHom (N' * p) ℓ ℤ (xint : Additive (Gamma0 (N' * p)) →+ ℤ)
            - (W.apOfModel ℓ) • (xint : Additive (Gamma0 (N' * p)) →+ ℤ)) = 0 := by
    intro ℓ hℓ hℓS hℓNp hgood
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓN : ¬ ℓ ∣ N' := fun h => hℓNp (dvd_mul_of_dvd_left h p)
    have he := hφeig ℓ hℓ hℓS hℓN hgood
    rw [AddMonoidHom.comp_sub, HeckeEis.postcomp_heckeOperatorHom, hxint, he, sub_eq_zero]
    refine AddMonoidHom.ext fun g => ?_
    rw [Submodule.coe_smul, AddMonoidHom.smul_apply, ← hxint, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.smul_apply, smul_eq_mul, zsmul_eq_mul]
    simp

  obtain ⟨𝔪₂, h1, h2, h3⟩ :=
    ModularCurve.Period.exists_ideal_heckeAlgebra_two_of_int_modp_eigenclass (N' * p) S₀ hS' p
      (fun ℓ => W.IsGoodPrimeFor ℓ) (fun ℓ => W.apOfModel ℓ) xint hx' heig'
  exact ⟨𝔪₂, h1, h2, fun ℓ hℓ hℓS hℓN hgood => h3 ℓ hℓ hℓS hℓN hgood⟩

end Arm

end P2mWeightTrade

open P2mWeightTrade in
theorem solution (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N') (hside : 3 < p ∨ 3 < N')
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (hS₀N : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S₀)
    (hS₀Δ : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S₀)
    (k : ℤ) (hk : k = 2 ∨ k = (p : ℤ) + 1)
    (𝔪ₖ : Ideal (heckeAlgebra N' k S₀)) (h𝔪ₖ : 𝔪ₖ.IsMaximal)
    (hp𝔪ₖ : (p : heckeAlgebra N' k S₀) ∈ 𝔪ₖ)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        heckeAlgebra.T hℓ hℓN hℓS -
          ((W.apOfModel ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪ₖ) :
    ∃ 𝔪₂ : Ideal (heckeAlgebra (N' * p) 2 S₀), 𝔪₂.IsMaximal ∧
      (p : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N' * p),
        W.IsGoodPrimeFor ℓ →
          heckeAlgebra.T hℓ hℓN hℓS -
            ((W.apOfModel ℓ : ℤ) : heckeAlgebra (N' * p) 2 S₀) ∈ 𝔪₂ := by
  rcases hk with hk | hk
  · subst hk
    exact WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two p W N' S₀ hS₀p
      hS₀N 𝔪ₖ h𝔪ₖ hp𝔪ₖ hocc
  · have hp : p.Prime := Fact.out
    have hk' : k = ((p - 1 : ℕ) : ℤ) + 2 := by
      have h1 : 1 ≤ p := hp.one_lt.le
      rw [hk, Nat.cast_sub h1]
      push_cast
      ring
    subst hk'
    exact weight_succ_arm p hp2 W N' hpN' S₀ hS₀p hS₀N (p - 1) rfl 𝔪ₖ h𝔪ₖ hp𝔪ₖ hocc

end S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ
end P2MW
export P2MW.S_WeierstrassCurve_exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ (solution)
