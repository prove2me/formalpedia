-- Prove2me | solution 1 for RibetIrr.span_range_baseChange_eq_top_of_companion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ee15fe8c-56b2-5bea-b0f1-131c1d31668e

import Theorems.Thm_RibetIrr_exists_dickson_eval_eq_of_span_ne_top
import Theorems.Thm_CuspForm_exists_isNewform_point_factor
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_RibetIrr_card_primes_apLarge_isBigO
import Theorems.Thm_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_Representation_span_range_baseChange_eq_top_iff
import Theorems.Thm_Representation_stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible
import Theorems.Thm_Representation_isIrreducible_of_span_range_eq_top
import Theorems.Thm_Representation_span_range_eq_top_of_isAbsolutelyIrreducible
import Definitions.Def_Representation_AbsolutelyIrreducible
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetIrr_span_range_baseChange_eq_top_of_companion
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "instance" "ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "Deformation.matrixRepresentation_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

open Polynomial
open scoped TensorProduct

section Endgame

set_option autoImplicit false

open Polynomial

namespace RibetIrr
p2m_export "RibetIrr" "exists_dickson_eval_eq_of_span_ne_top card_primes_apLarge_isBigO"
namespace TraceShape
p2m_open "RibetIrr"

variable {R : Type*} [CommRing R]

theorem dickson_one_eval_add (a x y : R) (h : x * y = a) :
    ∀ n : ℕ, (dickson 1 a n).eval (x + y) = x ^ n + y ^ n
  | 0 => by simp [dickson_zero]; norm_num
  | 1 => by simp [dickson_one]
  | n + 2 => by
    have h₁ := dickson_one_eval_add a x y h (n + 1)
    have h₀ := dickson_one_eval_add a x y h n
    simp only [dickson_add_two, eval_sub, eval_mul, eval_X, eval_C, h₁, h₀]
    rw [← h]; ring

theorem dickson_one_eval_eq_of_pow_eq (c u v : R) (M : ℕ) (huv : u * v = c)
    (hu : u ^ M = c ^ M) (hv : v ^ M = 1) :
    (dickson 1 c M).eval (u + v) = c ^ M + 1 := by
  rw [dickson_one_eval_add c u v huv M, hu, hv]

theorem dickson_one_eval_map {S : Type*} [CommRing S] (f : R →+* S) (c a : R) (M : ℕ)
    (h : (dickson 1 c M).eval a = c ^ M + 1) :
    (dickson 1 (f c) M).eval (f a) = f c ^ M + 1 := by
  rw [← map_dickson f, eval_map, eval₂_hom, h, map_add, map_pow, map_one]

theorem sub_one_le_norm_of_dickson_eval_eq (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (M : ℕ) (hM : M ≠ 0) (a : ℂ)
    (h : (dickson 1 (ℓ : ℂ) M).eval a = (ℓ : ℂ) ^ M + 1) :
    ℓ - 1 ≤ ‖a‖ := by

  obtain ⟨α, β, hsum, hprod⟩ : ∃ α β : ℂ, α + β = a ∧ α * β = ℓ := by
    have hdeg : 0 < (X ^ 2 - C a * X + C (ℓ : ℂ) : ℂ[X]).degree := by
      have : (X ^ 2 - C a * X + C (ℓ : ℂ) : ℂ[X]).degree = 2 := by
        compute_degree!
      rw [this]; norm_num
    obtain ⟨α, hα⟩ := Complex.exists_root hdeg
    have hα' : α ^ 2 - a * α + ℓ = 0 := by
      simpa [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] using hα
    exact ⟨α, a - α, by ring, by linear_combination -hα'⟩
  have hD : α ^ M + β ^ M = (ℓ : ℂ) ^ M + 1 := by
    rw [← dickson_one_eval_add (ℓ : ℂ) α β hprod M, hsum, h]
  have hpp : α ^ M * β ^ M = (ℓ : ℂ) ^ M := by rw [← mul_pow, hprod]

  have hquad : (α ^ M - 1) * (α ^ M - (ℓ : ℂ) ^ M) = 0 := by
    linear_combination (-1 : ℂ) * hpp + α ^ M * hD
  have hcases : α ^ M = 1 ∨ β ^ M = 1 := by
    rcases mul_eq_zero.mp hquad with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (by linear_combination hD - sub_eq_zero.mp h2)
  have hnorm : ‖α‖ * ‖β‖ = ℓ := by
    rw [← norm_mul, hprod, Complex.norm_real, Real.norm_of_nonneg hℓ]
  have hone : ∀ z : ℂ, z ^ M = 1 → ‖z‖ = 1 := fun z hz =>
    (pow_eq_one_iff_of_nonneg (norm_nonneg z) hM).mp (by rw [← norm_pow, hz, norm_one])

  have htri₁ : ‖β‖ - ‖α‖ ≤ ‖a‖ := by
    have := norm_sub_norm_le β (-α)
    rwa [norm_neg, sub_neg_eq_add, add_comm, hsum] at this
  have htri₂ : ‖α‖ - ‖β‖ ≤ ‖a‖ := by
    have := norm_sub_norm_le α (-β)
    rwa [norm_neg, sub_neg_eq_add, hsum] at this
  rcases hcases with h1 | h1
  · have hα1 := hone α h1
    rw [hα1, one_mul] at hnorm
    linarith
  · have hβ1 := hone β h1
    rw [hβ1, mul_one] at hnorm
    linarith

theorem injective_of_isIntegral_int {A B : Type*} [CommRing A] [IsDomain A]
    [Algebra.IsIntegral ℤ A] [Ring B] [CharZero B] (f : A →+* B) :
    Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  rw [hn]
  exact Ideal.zero_mem ⊥

theorem dickson_eval_eq_of_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (ℓ : ℤ) (M : ℕ) (a : A)
    (h : (dickson 1 ((ℓ : B)) M).eval (f a) = (ℓ : B) ^ M + 1) :
    (dickson 1 ((ℓ : A)) M).eval a = (ℓ : A) ^ M + 1 := by
  apply hf
  rw [map_add, map_pow, map_one, ← eval₂_hom, ← eval_map, map_dickson, map_intCast]
  exact h

end RibetIrr.TraceShape

open Finset CongruenceSubgroup

namespace RibetIrr
p2m_export "RibetIrr" "exists_dickson_eval_eq_of_span_ne_top card_primes_apLarge_isBigO"
namespace Endgame
p2m_open "RibetIrr"

lemma card_primes_window_le {Mg : ℕ} [NeZero Mg] (g : CuspForm (Gamma0 Mg) 2)
    (T : Finset ℕ) (K₀ : ℕ)
    (hK₀ : ∀ X : ℕ, ((Finset.Ioc (X / 3) X).filter
        fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ℝ) - 1 ≤ ‖ModularFormClass.qCoeff g ℓ‖).card ≤ K₀)
    (hge : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ T → (ℓ : ℝ) - 1 ≤ ‖ModularFormClass.qCoeff g ℓ‖)
    (X : ℕ) :
    ((Finset.Ioc (X / 3) X).filter Nat.Prime).card ≤ K₀ + T.card := by
  classical
  set S := (Finset.Ioc (X / 3) X).filter Nat.Prime

  calc S.card
      = (S.filter (· ∉ T)).card + (S.filter (· ∈ T)).card := by
        rw [← Finset.card_filter_add_card_filter_not (s := S) (p := (· ∈ T))]
        omega
    _ ≤ K₀ + T.card := by
        apply add_le_add
        ·
          refine le_trans (Finset.card_le_card ?_) (hK₀ X)
          intro ℓ hℓ
          simp only [Finset.mem_filter, S] at hℓ ⊢
          exact ⟨hℓ.1.1, hℓ.1.2, hge ℓ hℓ.1.2 hℓ.2⟩
        ·
          refine Finset.card_le_card ?_
          intro ℓ hℓ
          exact (Finset.mem_filter.mp hℓ).2

lemma sum_one_div_primes_le_of_window_bound (C : ℕ)
    (hwin : ∀ X : ℕ, ((Finset.Ioc (X / 3) X).filter Nat.Prime).card ≤ C)
    (s : Finset Nat.Primes) :
    ∑ p ∈ s, (1 : ℝ) / (p : ℕ) ≤ (C : ℝ) * (3 / 2) := by
  classical

  set kOf : Nat.Primes → ℕ := fun p => Nat.clog 3 (p : ℕ)
  have h3 : (1 : ℕ) < 3 := by norm_num
  have hkOf1 : ∀ p : Nat.Primes, 1 ≤ kOf p := fun p => Nat.clog_pos h3 p.2.one_lt

  have hpmem : ∀ p : Nat.Primes, (p : ℕ) ∈ Finset.Ioc (3 ^ (kOf p) / 3) (3 ^ (kOf p)) := by
    intro p
    have hpg : (1 : ℕ) < (p : ℕ) := p.2.one_lt
    rw [Finset.mem_Ioc]
    refine ⟨?_, Nat.le_pow_clog h3 (p : ℕ)⟩
    have hk := hkOf1 p
    have hdiv : (3 : ℕ) ^ kOf p / 3 = 3 ^ (kOf p - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
      exact Nat.mul_div_cancel _ (by norm_num)
    rw [hdiv]
    exact Nat.pow_pred_clog_lt_self h3 hpg

  have hbnd : ∀ p ∈ s, (1 : ℝ) / (p : ℕ) ≤ (1 : ℝ) / 3 ^ (kOf p - 1) := by
    intro p _
    have hlt : (3 : ℕ) ^ (kOf p - 1) < (p : ℕ) := Nat.pow_pred_clog_lt_self h3 p.2.one_lt
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast hlt.le
  calc ∑ p ∈ s, (1 : ℝ) / (p : ℕ)
      ≤ ∑ p ∈ s, (1 : ℝ) / 3 ^ (kOf p - 1) := Finset.sum_le_sum hbnd
    _ = ∑ k ∈ s.image kOf, ∑ p ∈ s.filter (kOf · = k), (1 : ℝ) / 3 ^ (k - 1) := by
        rw [← Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem kOf hp)]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p hp => ?_
        rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ k ∈ s.image kOf,
          ((s.filter (kOf · = k)).card : ℝ) * ((1 : ℝ) / 3 ^ (k - 1)) := by
        simp_rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ s.image kOf, (C : ℝ) * ((1 : ℝ) / 3 ^ (k - 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_right _ (by positivity)

        have hsub : (s.filter (kOf · = k)).image (Subtype.val : Nat.Primes → ℕ)
            ⊆ (Finset.Ioc (3 ^ k / 3) (3 ^ k)).filter Nat.Prime := by
          intro ℓ hℓ
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hℓ
          have hpfilt := Finset.mem_filter.mp hp
          rw [Finset.mem_filter]
          exact ⟨hpfilt.2 ▸ hpmem p, p.2⟩
        have hcard :=
          Finset.card_le_card hsub |>.trans (hwin (3 ^ k))
        rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
        exact_mod_cast hcard
    _ = (C : ℝ) * ∑ k ∈ s.image kOf, (1 : ℝ) / 3 ^ (k - 1) := by
        rw [← Finset.mul_sum]
    _ ≤ (C : ℝ) * (3 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)

        have hinj : ∀ a ∈ s.image kOf, ∀ b ∈ s.image kOf, a - 1 = b - 1 → a = b := by
          intro a ha b hb hab
          obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hb
          have h1a := hkOf1 p; have h1b := hkOf1 q
          omega
        calc ∑ k ∈ s.image kOf, (1 : ℝ) / 3 ^ (k - 1)
            = ∑ k ∈ s.image kOf, ((1 : ℝ) / 3) ^ (k - 1) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [one_div_pow]
          _ = ∑ j ∈ (s.image kOf).image (· - 1), ((1 : ℝ) / 3) ^ j :=
              (Finset.sum_image hinj).symm
          _ ≤ ∑' j : ℕ, ((1 : ℝ) / 3) ^ j := by
              apply Summable.sum_le_tsum _ (fun _ _ => by positivity)
              exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
          _ = (1 - 1 / 3)⁻¹ :=
              tsum_geometric_of_lt_one (by norm_num) (by norm_num)
          _ = 3 / 2 := by norm_num

theorem false_of_forall_prime_qCoeff_ge
    (Mg : ℕ) [NeZero Mg] (g : CuspForm (Gamma0 Mg) 2)
    (T : Finset ℕ)
    (hge : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ T → (ℓ : ℝ) - 1 ≤ ‖ModularFormClass.qCoeff g ℓ‖) :
    False := by
  obtain ⟨K₀, hK₀⟩ := RibetIrr.card_primes_apLarge_isBigO Mg g
  have hwin := card_primes_window_le g T K₀ hK₀ hge
  apply Nat.Primes.not_summable_one_div
  exact summable_of_sum_le (c := ((K₀ + T.card : ℕ) : ℝ) * (3 / 2))
    (fun p => by positivity)
    (fun s => sum_one_div_primes_le_of_window_bound (K₀ + T.card) hwin s)

end RibetIrr.Endgame

namespace RibetIrr
p2m_export "RibetIrr" "exists_dickson_eval_eq_of_span_ne_top card_primes_apLarge_isBigO"
namespace Endgame
p2m_open "RibetIrr"

open RibetIrr.TraceShape Polynomial

lemma isIntegral_int_range_chig
    (Mg : ℕ) [NeZero Mg] (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra Mg 2 (↑S : Set ℕ) →+* ℂ) :
    Algebra.IsIntegral ℤ chig.range := by
  have hfin : Module.Finite ℤ (CuspForm.heckeAlgebra Mg 2 (↑S : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two Mg (↑S : Set ℕ)
  have hsurj := chig.rangeRestrict_surjective
  haveI : Module.Finite ℤ chig.range :=
    Module.Finite.of_surjective chig.rangeRestrict.toIntAlgHom.toLinearMap hsurj
  infer_instance

theorem false_of_dickson_eval_eq_hecke
    (N : ℕ) [NeZero N] (S : Finset ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [CharZero 𝒪']
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (m : ℕ) (hm : m ≠ 0) (E : Finset ℕ)
    (hD : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), ℓ ∉ E →
      (dickson 1 ((ℓ : 𝒪')) m).eval (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
        = (ℓ : 𝒪') ^ m + 1) :
    False := by
  obtain ⟨Mg, hMgNZ, hMgN, g, -, chig, hchig, iota, hiota⟩ :=
    CuspForm.exists_isNewform_point_factor N S hNS 𝒪' χ
  haveI : NeZero Mg := hMgNZ

  haveI := isIntegral_int_range_chig Mg S chig
  have hiota_inj : Function.Injective iota := injective_of_isIntegral_int iota

  apply false_of_forall_prime_qCoeff_ge Mg g (E ∪ S ∪ N.primeFactors)
  intro ℓ hℓp hℓnot
  simp only [Finset.mem_union, not_or] at hℓnot
  obtain ⟨⟨hℓE, hℓS'⟩, hℓNpf⟩ := hℓnot
  have hℓN : ¬ ℓ ∣ N := fun h => hℓNpf (Nat.mem_primeFactors.mpr ⟨hℓp, h, NeZero.ne N⟩)
  have hℓS : ℓ ∉ (↑S : Set ℕ) := by simpa using hℓS'
  have hℓMg : ¬ ℓ ∣ Mg := fun h => hℓN (h.trans hMgN)

  have h1 : (dickson 1 ((ℓ : 𝒪')) m).eval
      (iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓp hℓMg hℓS)))
      = (ℓ : 𝒪') ^ m + 1 := by
    rw [hiota ℓ hℓp hℓN hℓS]
    exact hD ℓ hℓp hℓN hℓS hℓE
  have h2 : (dickson 1 ((ℓ : ↥chig.range)) m).eval
      (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓp hℓMg hℓS))
      = (ℓ : ↥chig.range) ^ m + 1 :=
    dickson_eval_eq_of_injective iota hiota_inj (ℓ : ℤ) m _ (by simpa using h1)
  have h3 : (dickson 1 ((ℓ : ℂ)) m).eval
      (chig (CuspForm.heckeAlgebra.T hℓp hℓMg hℓS)) = (ℓ : ℂ) ^ m + 1 := by
    have := dickson_one_eval_map (chig.range.subtype) (ℓ : ↥chig.range) _ m h2
    simpa [Subring.coe_subtype, RingHom.coe_rangeRestrict, map_natCast] using this
  rw [hchig ℓ hℓp hℓMg hℓS] at h3
  exact sub_one_le_norm_of_dickson_eval_eq (ℓ : ℝ) (Nat.cast_nonneg ℓ) m hm _
    (by push_cast at h3 ⊢; exact h3)

end RibetIrr.Endgame

end Endgame

noncomputable section

namespace RibetIrr
p2m_export "RibetIrr" "exists_dickson_eval_eq_of_span_ne_top card_primes_apLarge_isBigO"
namespace Transfer
p2m_open "RibetIrr"

open Polynomial

theorem forall_stable_eq_bot_or_top_of_isIrreducible
    {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (hirr : ρ.IsIrreducible) :
    ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  rcases hirr.eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

theorem isIrreducible_of_forall_stable_eq_bot_or_top
    {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K G V)
    (h : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ρ.IsIrreducible := by
  haveI : Nontrivial (Subrepresentation ρ) := by
    obtain ⟨x, hx0⟩ := exists_ne (0 : V)
    refine ⟨⟨⊥, ⊤, fun hbt => hx0 ?_⟩⟩
    have h' : (⊥ : Submodule K V) = ⊤ := congrArg Subrepresentation.toSubmodule hbt
    exact (Submodule.mem_bot K).mp (h'.symm ▸ Submodule.mem_top)
  refine { eq_bot_or_eq_top := fun σ => ?_ }
  rcases h σ.toSubmodule (fun g v hv => σ.apply_mem_toSubmodule g hv) with h' | h'
  · exact Or.inl (Subrepresentation.toSubmodule_injective h')
  · exact Or.inr (Subrepresentation.toSubmodule_injective h')

theorem trace_eq_and_det_eq_of_charpoly_eq
    {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] [Module.Free K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W] [Module.Free K W]
    (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hfrV : Module.finrank K V = 2) (hfrW : Module.finrank K W = 2)
    (h : LinearMap.charpoly f = LinearMap.charpoly g) :
    LinearMap.trace K V f = LinearMap.trace K W g ∧ LinearMap.det f = LinearMap.det g := by
  have bV := Module.Free.chooseBasis K V
  have bW := Module.Free.chooseBasis K W
  have hcV : Fintype.card (Module.Free.ChooseBasisIndex K V) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; exact hfrV
  have hcW : Fintype.card (Module.Free.ChooseBasisIndex K W) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; exact hfrW
  haveI : Nonempty (Module.Free.ChooseBasisIndex K V) :=
    Fintype.card_pos_iff.mp (by rw [hcV]; norm_num)
  haveI : Nonempty (Module.Free.ChooseBasisIndex K W) :=
    Fintype.card_pos_iff.mp (by rw [hcW]; norm_num)
  have htrV : LinearMap.trace K V f = -(LinearMap.charpoly f).coeff 1 := by
    rw [LinearMap.trace_eq_matrix_trace K bV, Matrix.trace_eq_neg_charpoly_coeff,
      LinearMap.charpoly_toMatrix, hcV]
  have htrW : LinearMap.trace K W g = -(LinearMap.charpoly g).coeff 1 := by
    rw [LinearMap.trace_eq_matrix_trace K bW, Matrix.trace_eq_neg_charpoly_coeff,
      LinearMap.charpoly_toMatrix, hcW]
  have hdV : LinearMap.det f = (LinearMap.charpoly f).coeff 0 := by
    rw [← LinearMap.det_toMatrix bV, Matrix.det_eq_sign_charpoly_coeff,
      LinearMap.charpoly_toMatrix, hcV]
    norm_num
  have hdW : LinearMap.det g = (LinearMap.charpoly g).coeff 0 := by
    rw [← LinearMap.det_toMatrix bW, Matrix.det_eq_sign_charpoly_coeff,
      LinearMap.charpoly_toMatrix, hcW]
    norm_num
  exact ⟨by rw [htrV, htrW, h], by rw [hdV, hdW, h]⟩

private theorem isIrreducible_baseChange_of_charpoly_eq
    {K G V W : Type} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K G V) (ρχ : Representation K G W)
    (hfrV : Module.finrank K V = 2) (hfrW : Module.finrank K W = 2)
    (hch : ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (ρχ g))
    (hχ : Submodule.span K (Set.range ⇑ρχ) = ⊤)
    (k' : Type) [Field k'] [Algebra K k'] :
    (Representation.baseChange k' ρ).IsIrreducible := by
  have hfrV' : Module.finrank k' (k' ⊗[K] V) = 2 := by
    rw [Module.finrank_baseChange, hfrV]
  have hfrW' : Module.finrank k' (k' ⊗[K] W) = 2 := by
    rw [Module.finrank_baseChange, hfrW]
  haveI : Nontrivial (k' ⊗[K] V) := by
    have h2 : 0 < Module.finrank k' (k' ⊗[K] V) := by rw [hfrV']; norm_num
    exact Module.nontrivial_of_finrank_pos h2
  haveI : Nontrivial (k' ⊗[K] W) := by
    have h2 : 0 < Module.finrank k' (k' ⊗[K] W) := by rw [hfrW']; norm_num
    exact Module.nontrivial_of_finrank_pos h2
  have hχ' : Submodule.span k'
      (Set.range ⇑(Representation.baseChange k' ρχ)) = ⊤ := by
    have h := (Representation.span_range_baseChange_eq_top_iff (K := k') ρχ).mpr hχ
    exact h
  have hirrχ : (Representation.baseChange k' ρχ).IsIrreducible :=
    Representation.isIrreducible_of_span_range_eq_top _ hχ'
  have hstχ := forall_stable_eq_bot_or_top_of_isIrreducible _ hirrχ
  have hch' : ∀ g, LinearMap.charpoly ((Representation.baseChange k' ρ) g) =
      LinearMap.charpoly ((Representation.baseChange k' ρχ) g) := by
    intro g
    show LinearMap.charpoly ((ρ g).baseChange k') =
      LinearMap.charpoly ((ρχ g).baseChange k')
    rw [LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange, hch g]
  have htd : ∀ g, LinearMap.trace k' (k' ⊗[K] V) ((Representation.baseChange k' ρ) g) =
        LinearMap.trace k' (k' ⊗[K] W) ((Representation.baseChange k' ρχ) g) ∧
      LinearMap.det ((Representation.baseChange k' ρ) g) =
        LinearMap.det ((Representation.baseChange k' ρχ) g) :=
    fun g => trace_eq_and_det_eq_of_charpoly_eq _ _ hfrV' hfrW' (hch' g)
  have hst₂ := Representation.stable_eq_bot_or_top_of_trace_eq_of_det_eq_of_irreducible
    (Representation.baseChange k' ρχ)
    (Representation.baseChange k' ρ) hfrW' hfrV' hstχ
    (fun g => ((htd g).1).symm) (fun g => ((htd g).2).symm)
  exact isIrreducible_of_forall_stable_eq_bot_or_top _ hst₂

theorem span_range_eq_top_of_charpoly_eq_of_span_range_eq_top
    {K G V W : Type} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K G V) (ρχ : Representation K G W)
    (hfrV : Module.finrank K V = 2) (hfrW : Module.finrank K W = 2)
    (hch : ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (ρχ g))
    (hχ : Submodule.span K (Set.range ⇑ρχ) = ⊤) :
    Submodule.span K (Set.range ⇑ρ) = ⊤ := by
  haveI : Representation.IsAbsolutelyIrreducible.{0} ρ :=
    ⟨fun k' fk' ak' =>
      @isIrreducible_baseChange_of_charpoly_eq K G V W _ _ _ _ _ _ _ _
        ρ ρχ hfrV hfrW hch hχ k' fk' ak'⟩
  have h := Representation.span_range_eq_top_of_isAbsolutelyIrreducible ρ
  exact h

end RibetIrr.Transfer

end

namespace RibetIrr
p2m_export "RibetIrr" "exists_dickson_eval_eq_of_span_ne_top card_primes_apLarge_isBigO"
namespace Companion
p2m_open "RibetIrr"

open IsLocalRing

noncomputable def genAction {A : Type} [CommRing A] [IsLocalRing A] (τ : GaloisRepAdic A)
    (R : Type) [CommRing R] [Algebra A R] :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End R (R ⊗[A] τ.V) where
  toFun σ := (τ.ρ σ).baseChange R
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' σ σ' := by rw [map_mul, LinearMap.baseChange_mul]

theorem exists_genericFibre_equiv {A : Type} [CommRing A] [IsLocalRing A] {B : Type}
    [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (τ : GaloisRepAdic A)
    (L : Type) [Field L] [Algebra B L] [Algebra A L]
    (hcomp : ∀ a, algebraMap A L a = algebraMap B L (φ a)) :
    ∃ e : L ⊗[B] (τ.baseChangeAlong φ hφ).V ≃ₗ[L] L ⊗[A] τ.V,
      ∀ σ x, e (((τ.baseChangeAlong φ hφ).ρ σ).baseChange L x) =
        (τ.ρ σ).baseChange L (e x) := by
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq hcomp
  let e : L ⊗[B] (B ⊗[A] τ.V) ≃ₗ[L] L ⊗[A] τ.V :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B L L τ.V
  have key : ∀ σ (x : L ⊗[B] (B ⊗[A] τ.V)),
      e (((τ.ρ σ).baseChange B).baseChange L x) = (τ.ρ σ).baseChange L (e x) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul l y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [LinearMap.baseChange_tmul] at hx hy ⊢
        simp only [map_add, TensorProduct.tmul_add, hx, hy]
      | tmul b v =>
        simp [e, LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  exact ⟨e, key⟩

theorem span_range_eq_top_of_equiv {R : Type} [CommRing R] {V W G : Type} [AddCommGroup V]
    [Module R V] [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) (f : G → Module.End R V)
    (g : G → Module.End R W) (hfg : ∀ σ x, e (f σ x) = g σ (e x))
    (h : Submodule.span R (Set.range f) = ⊤) : Submodule.span R (Set.range g) = ⊤ := by
  have hg : g = ⇑((LinearEquiv.conj e : Module.End R V ≃ₗ[R] Module.End R W) :
      Module.End R V →ₗ[R] Module.End R W) ∘ f := by
    funext σ; apply LinearMap.ext; intro y
    show g σ y = (LinearEquiv.conj e (f σ)) y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, hfg, LinearEquiv.apply_symm_apply]
  rw [hg, Set.range_comp, Submodule.span_image, h, Submodule.map_top, LinearMap.range_eq_top]
  exact fun y => ⟨(LinearEquiv.conj e).symm y, by simp⟩

theorem exists_cancel_equiv (A K L V : Type) [CommRing A] [Field K] [Field L] [Algebra A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [AddCommGroup V] [Module A V] :
    ∃ e : L ⊗[K] (K ⊗[A] V) ≃ₗ[L] L ⊗[A] V,
      ∀ (f : Module.End A V) x, e ((f.baseChange K).baseChange L x) = f.baseChange L (e x) := by
  let e : L ⊗[K] (K ⊗[A] V) ≃ₗ[L] L ⊗[A] V :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A K L L V
  refine ⟨e, fun f x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul l y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [LinearMap.baseChange_tmul] at hx hy ⊢
      simp only [map_add, TensorProduct.tmul_add, hx, hy]
    | tmul b v =>
      simp [e, LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

theorem charpoly_baseChangeAlong {A : Type} [CommRing A] [IsLocalRing A] {B : Type}
    [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (τ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly ((τ.baseChangeAlong φ hφ).ρ σ) = (LinearMap.charpoly (τ.ρ σ)).map φ := by
  letI : Algebra A B := φ.toAlgebra
  show LinearMap.charpoly ((τ.ρ σ).baseChange B) = _
  rw [LinearMap.charpoly_baseChange]; rfl

theorem span_range_baseChange_eq_top_of_companion
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (ρ : GaloisRepAdic 𝒪')
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪')))
    (𝒪'' : Type) [CommRing 𝒪''] [IsDomain 𝒪''] [IsDiscreteValuationRing 𝒪'']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪'') 𝒪'']
    [Finite (IsLocalRing.ResidueField 𝒪'')] [CharZero 𝒪'']
    (φ : 𝒪' →+* 𝒪'') (hφ : IsLocalHom φ)
    (K'' : Type) [Field K''] [Algebra 𝒪'' K''] [IsFractionRing 𝒪'' K''] [Algebra K K'']
    [Algebra 𝒪' K''] [IsScalarTower 𝒪' K K'']
    (hcomp : ∀ a, algebraMap 𝒪' K'' a = algebraMap 𝒪'' K'' (φ a))
    (ρχ : GaloisRepAdic 𝒪'') (hp : (p : 𝒪'') ∈ IsLocalRing.maximalIdeal 𝒪'')
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρχ.IsUnramifiedAt q)
    (hloc : ∀ (L : Type) [Field L] [Algebra 𝒪'' L] [Algebra K'' L] [IsScalarTower 𝒪'' K'' L]
      [FiniteDimensional K'' L] (W : Submodule L (L ⊗[𝒪''] ρχ.V)), Module.finrank L W = 1 →
      (∀ σ, ∀ w ∈ W, (ρχ.ρ σ).baseChange L w ∈ W) →
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, ((ρχ.ρ σ).baseChange L ^ n) w = w) ∨
        (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v, ((ρχ.ρ σ).baseChange L ^ n) v - v ∈ W))
    (hfrobχ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρχ.ρ σ) =
              X ^ 2 - C (φ (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) * X + C ((ℓ : 𝒪''))) :
    Submodule.span K (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ.ρ σ).baseChange K) = ⊤ := by
  classical

  have hout : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S ∪ N.primeFactors → ¬ ℓ ∣ N ∧ ℓ ∉ (↑S : Set ℕ) := by
    intro ℓ hℓ h
    simp only [Finset.mem_union, not_or] at h
    exact ⟨fun hd => h.2 (Nat.mem_primeFactors.mpr ⟨hℓ, hd, NeZero.ne N⟩), by simpa using h.1⟩

  have hχtop : Submodule.span K''
      (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
        (ρχ.ρ σ).baseChange K'') = ⊤ := by
    by_contra hne
    let a : ℕ → 𝒪'' := fun ℓ =>
      if h : ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ (↑S : Set ℕ) then
        φ (χ (CuspForm.heckeAlgebra.T h.1 h.2.1 h.2.2)) else 0
    have ha : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        a ℓ = φ (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := by
      intro ℓ hℓ hℓN hℓS
      simp only [a, dif_pos (show ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ (↑S : Set ℕ) from ⟨hℓ, hℓN, hℓS⟩)]
    have hfrob' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S ∪ N.primeFactors →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρχ.ρ σ) = X ^ 2 - C (a ℓ) * X + C ((ℓ : 𝒪'')) := by
      intro ℓ hℓ hℓE A hA σ hσ
      obtain ⟨hℓN, hℓS⟩ := hout ℓ hℓ hℓE
      rw [ha ℓ hℓ hℓN hℓS]
      exact hfrobχ ℓ hℓ hℓN hℓS A hA σ hσ
    obtain ⟨m, hm0, E, hE⟩ := RibetIrr.exists_dickson_eval_eq_of_span_ne_top p N 𝒪'' K'' ρχ hp
      (NeZero.ne N) hunr hloc a (S ∪ N.primeFactors) hfrob' hne
    refine RibetIrr.Endgame.false_of_dickson_eval_eq_hecke N S hNS 𝒪'' (φ.comp χ) m hm0
      (E ∪ (S ∪ N.primeFactors)) ?_
    intro ℓ hℓ hℓN hℓS hℓE
    simp only [Finset.mem_union, not_or] at hℓE
    have h1 := hE ℓ hℓ hℓE.1
    rw [ha ℓ hℓ hℓN hℓS] at h1
    simpa using h1

  have hch : ∀ σ, LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) =
      LinearMap.charpoly (ρχ.ρ σ) := by
    refine GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq _ _ (S ∪ N.primeFactors) ?_
    intro ℓ hℓ hℓE B τ hB hτ
    obtain ⟨hℓN, hℓS⟩ := hout ℓ hℓ hℓE
    rw [charpoly_baseChangeAlong, hfrob ℓ hℓ hℓN hℓS B hB τ hτ, hfrobχ ℓ hℓ hℓN hℓS B hB τ hτ]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

  have hfr1 : Module.finrank K'' (K'' ⊗[𝒪''] (ρ.baseChangeAlong φ hφ).V) = 2 := by
    rw [Module.finrank_baseChange, (ρ.baseChangeAlong φ hφ).finrank_eq]
  have hfr2 : Module.finrank K'' (K'' ⊗[𝒪''] ρχ.V) = 2 := by
    rw [Module.finrank_baseChange, ρχ.finrank_eq]
  have hchK : ∀ g, LinearMap.charpoly (genAction (ρ.baseChangeAlong φ hφ) K'' g) =
      LinearMap.charpoly (genAction ρχ K'' g) := by
    intro g
    show LinearMap.charpoly (((ρ.baseChangeAlong φ hφ).ρ g).baseChange K'') =
      LinearMap.charpoly ((ρχ.ρ g).baseChange K'')
    rw [LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange, hch]
  have hχK : Submodule.span K'' (Set.range ⇑(genAction ρχ K'')) = ⊤ := hχtop
  have htop'' : Submodule.span K'' (Set.range ⇑(genAction (ρ.baseChangeAlong φ hφ) K'')) = ⊤ :=
    RibetIrr.Transfer.span_range_eq_top_of_charpoly_eq_of_span_range_eq_top
      (genAction (ρ.baseChangeAlong φ hφ) K'') (genAction ρχ K'') hfr1 hfr2 hchK hχK

  obtain ⟨e, he⟩ := exists_genericFibre_equiv φ hφ ρ K'' hcomp
  have htopK'' : Submodule.span K''
      (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
        (ρ.ρ σ).baseChange K'') = ⊤ :=
    span_range_eq_top_of_equiv e (fun σ => ((ρ.baseChangeAlong φ hφ).ρ σ).baseChange K'')
      (fun σ => (ρ.ρ σ).baseChange K'') he htop''
  obtain ⟨e₂, he₂⟩ := exists_cancel_equiv 𝒪' K K'' ρ.V
  have htop2 : Submodule.span K''
      (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
        ((ρ.ρ σ).baseChange K).baseChange K'') = ⊤ :=
    span_range_eq_top_of_equiv e₂.symm (fun σ => (ρ.ρ σ).baseChange K'')
      (fun σ => ((ρ.ρ σ).baseChange K).baseChange K'')
      (fun σ x => by
        apply e₂.injective
        rw [LinearEquiv.apply_symm_apply, he₂, LinearEquiv.apply_symm_apply]) htopK''
  exact (Representation.span_range_baseChange_eq_top_iff (K := K'') (genAction ρ K)).mp htop2

end RibetIrr.Companion

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (ρ : GaloisRepAdic 𝒪')
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : 𝒪')))
    (𝒪'' : Type) [CommRing 𝒪''] [IsDomain 𝒪''] [IsDiscreteValuationRing 𝒪'']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪'') 𝒪'']
    [Finite (IsLocalRing.ResidueField 𝒪'')] [CharZero 𝒪'']
    (φ : 𝒪' →+* 𝒪'') (hφ : IsLocalHom φ)
    (K'' : Type) [Field K''] [Algebra 𝒪'' K''] [IsFractionRing 𝒪'' K''] [Algebra K K'']
    [Algebra 𝒪' K''] [IsScalarTower 𝒪' K K'']
    (hcomp : ∀ a, algebraMap 𝒪' K'' a = algebraMap 𝒪'' K'' (φ a))
    (ρχ : GaloisRepAdic 𝒪'') (hp : (p : 𝒪'') ∈ IsLocalRing.maximalIdeal 𝒪'')
    (hunr : ∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρχ.IsUnramifiedAt q)
    (hloc : ∀ (L : Type) [Field L] [Algebra 𝒪'' L] [Algebra K'' L] [IsScalarTower 𝒪'' K'' L]
      [FiniteDimensional K'' L] (W : Submodule L (L ⊗[𝒪''] ρχ.V)), Module.finrank L W = 1 →
      (∀ σ, ∀ w ∈ W, (ρχ.ρ σ).baseChange L w ∈ W) →
      (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, ((ρχ.ρ σ).baseChange L ^ n) w = w) ∨
        (∃ n : ℕ, 0 < n ∧ ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v, ((ρχ.ρ σ).baseChange L ^ n) v - v ∈ W))
    (hfrobχ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρχ.ρ σ) =
              X ^ 2 - C (φ (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) * X + C ((ℓ : 𝒪''))) :
    Submodule.span K (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ.ρ σ).baseChange K) = ⊤ :=
  RibetIrr.Companion.span_range_baseChange_eq_top_of_companion p N S hNS 𝒪' K χ ρ hfrob 𝒪'' φ hφ K''
    hcomp ρχ hp hunr hloc hfrobχ

end S_RibetIrr_span_range_baseChange_eq_top_of_companion
end P2MW
export P2MW.S_RibetIrr_span_range_baseChange_eq_top_of_companion (solution)
