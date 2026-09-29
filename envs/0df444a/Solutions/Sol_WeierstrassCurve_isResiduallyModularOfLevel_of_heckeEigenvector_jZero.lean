-- Prove2me | solution 1 for WeierstrassCurve.isResiduallyModularOfLevel_of_heckeEigenvector_jZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5d1dbab0-d02d-53c8-8c31-39b21a40209a

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_ModularCurve_exists_injective_ringHom_adjoin_heckeOperatorBar_cuspForm
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_heckeEigenvector_jZero
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.cuspCount_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe"
p2m_attr_erase "simp" "ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

open ModularCurve

namespace W7X

variable {N₀ : ℕ} {p : ℕ} {W : WeierstrassCurve ℤ} {S : Finset Nat.Primes}

theorem not_dvd_level (hS : ∀ ℓ : Nat.Primes, ℓ ∈ S ↔ (ℓ : ℕ) ∣ N₀ * p * W.Δ.natAbs)
    {ℓ : Nat.Primes} (hℓ : ℓ ∉ S) : ¬ (ℓ : ℕ) ∣ N₀ := fun h =>
  hℓ ((hS ℓ).mpr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _))

def badSet (N₀ p : ℕ) (W : WeierstrassCurve ℤ) : Set ℕ := {n | n ∣ N₀ * p * W.Δ.natAbs}

theorem not_mem_badSet (hS : ∀ ℓ : Nat.Primes, ℓ ∈ S ↔ (ℓ : ℕ) ∣ N₀ * p * W.Δ.natAbs)
    {ℓ : Nat.Primes} (hℓ : ℓ ∉ S) : (ℓ : ℕ) ∉ badSet N₀ p W := fun h => hℓ ((hS ℓ).mpr h)

variable [NeZero N₀] (hS : ∀ ℓ : Nat.Primes, ℓ ∈ S ↔ (ℓ : ℕ) ∣ N₀ * p * W.Δ.natAbs)

open Classical in

noncomputable def gen : Nat.Primes → CuspForm.heckeAlgebra N₀ 2 (badSet N₀ p W) :=
  fun ℓ => if h : ℓ ∈ S then 0
    else CuspForm.heckeAlgebra.T (S := badSet N₀ p W) ℓ.prop (not_dvd_level hS h) (not_mem_badSet hS h)

theorem gen_of_not_mem {ℓ : Nat.Primes} (hℓ : ℓ ∉ S) :
    ((gen hS ℓ : CuspForm.heckeAlgebra N₀ 2 (badSet N₀ p W)) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2))
      = CuspForm.heckeTLin 2 ℓ.prop (not_dvd_level hS hℓ) := by
  simp [gen, hℓ]

theorem gen_of_mem {ℓ : Nat.Primes} (hℓ : ℓ ∈ S) : gen hS ℓ = 0 := by
  simp [gen, hℓ]

noncomputable def ψ : HeckeAlg →ₐ[ℤ] CuspForm.heckeAlgebra N₀ 2 (badSet N₀ p W) :=
  MvPolynomial.aeval (R := ℤ) (gen hS)

theorem ψ_surjective : Function.Surjective (ψ hS) := by
  rintro ⟨t, ht⟩
  induction ht using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
    · have hℓ' : (⟨ℓ, hℓ⟩ : Nat.Primes) ∉ S := fun h => hℓS ((hS _).mp h)
      refine ⟨MvPolynomial.X ⟨ℓ, hℓ⟩, Subtype.ext ?_⟩
      rw [ψ, MvPolynomial.aeval_X, gen_of_not_mem hS hℓ']
    · exact absurd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hqN _) _ : q ∈ badSet N₀ p W) hqS
  | algebraMap r => exact ⟨MvPolynomial.C r, by rw [ψ, MvPolynomial.algHom_C]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P + Q, by rw [map_add, hP, hQ]; rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P * Q, by rw [map_mul, hP, hQ]; rfl⟩

open Classical in

noncomputable def κ (S : Finset Nat.Primes) : HeckeAlg →ₐ[ℤ] HeckeAlg :=
  MvPolynomial.aeval (R := ℤ) (fun ℓ => if ℓ ∈ S then 0 else MvPolynomial.X ℓ)

theorem κ_X_of_not_mem {ℓ : Nat.Primes} (hℓ : ℓ ∉ S) : κ S (MvPolynomial.X ℓ) = MvPolynomial.X ℓ := by
  simp [κ, hℓ]

theorem κ_X_of_mem {ℓ : Nat.Primes} (hℓ : ℓ ∈ S) : κ S (MvPolynomial.X ℓ) = 0 := by
  simp [κ, hℓ]

theorem ψ_comp_κ : (ψ hS).comp (κ S) = ψ hS := by
  apply MvPolynomial.algHom_ext
  intro ℓ
  by_cases hℓ : ℓ ∈ S
  · rw [AlgHom.comp_apply, κ_X_of_mem hℓ, map_zero, ψ, MvPolynomial.aeval_X, gen_of_mem hS hℓ]
  · rw [AlgHom.comp_apply, κ_X_of_not_mem hℓ]

theorem mvPolynomial_int_ringHom_ext {σ A : Type*} [Semiring A]
    {f g : MvPolynomial σ ℤ →+* A} (hX : ∀ i, f (MvPolynomial.X i) = g (MvPolynomial.X i)) :
    f = g :=
  MvPolynomial.ringHom_ext
    (fun r => RingHom.congr_fun (RingHom.ext_int (f.comp MvPolynomial.C) (g.comp MvPolynomial.C)) r)
    hX

theorem comp_κ_eq
    {A : Type*} [Semiring A] (F₁ F₂ : HeckeAlg →+* A)
    (h₁ : ∀ ℓ : Nat.Primes, ℓ ∉ S → F₁ (heckeGen ℓ) = F₂ (heckeGen ℓ))
    (h₂ : ∀ ℓ : Nat.Primes, ℓ ∈ S → F₂ (heckeGen ℓ) = 0) (P : HeckeAlg) :
    F₁ (κ S P) = F₂ P := by
  have hcomp : F₁.comp (κ S).toRingHom = F₂ := by
    refine mvPolynomial_int_ringHom_ext fun ℓ => ?_
    by_cases hℓ : ℓ ∈ S
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, κ_X_of_mem hℓ, map_zero,
        ← heckeGen, h₂ ℓ hℓ]
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, κ_X_of_not_mem hℓ,
        ← heckeGen, h₁ ℓ hℓ]
  exact RingHom.congr_fun hcomp P

end W7X

open W7X in
set_option maxHeartbeats 3200000 in
theorem solution
    (N₀ : ℕ) [NeZero N₀] {p : ℕ} (hp : p.Prime)
    (hin : ModularCurve.HeckeInputsAll N₀) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N₀)
    (W : WeierstrassCurve ℤ)
    (S : Finset Nat.Primes) (hS : ∀ ℓ : Nat.Primes, ℓ ∈ S ↔ (ℓ : ℕ) ∣ N₀ * p * W.Δ.natAbs)
    (y : ModularCurve.JZero N₀) (hy : y ≠ 0) (hpy : (p : ℤ) • y = 0)
    (heig : ∀ ℓ : Nat.Primes, ℓ ∉ S →
      (letI := ModularCurve.heckeModuleBar N₀;
        (ModularCurve.heckeGen ℓ - MvPolynomial.C (W.apOfModel ℓ)) • y) = 0) :
    W.IsResiduallyModularOfLevel p N₀ := by
  letI : Module HeckeAlg (JZero N₀) := ModularCurve.heckeModuleBar N₀

  obtain ⟨Φ, hΦinj, hΦ⟩ :=
    ModularCurve.exists_injective_ringHom_adjoin_heckeOperatorBar_cuspForm N₀ hin hcomm

  set 𝕋' := CuspForm.heckeAlgebra N₀ 2 (badSet N₀ p W) with h𝕋'
  set A : Ideal HeckeAlg := (Ideal.torsionOf HeckeAlg (JZero N₀) y).comap (κ S) with hA
  set 𝔞 : Ideal 𝕋' := A.map (ψ hS) with h𝔞
  have hmemA : ∀ t : HeckeAlg, t ∈ A ↔ (κ S t) • y = 0 := fun t => by
    rw [hA, Ideal.mem_comap, Ideal.mem_torsionOf_iff]

  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : HeckeAlg →+* Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2),
      ∀ s, F₁ s = Φ (heckeEvalBarAux hcomm s) :=
    ⟨Φ.comp (heckeEvalBarAux hcomm).toRingHom, fun _ => rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : HeckeAlg →+* Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2),
      ∀ s, F₂ s = ((ψ hS s : 𝕋') : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2)) :=
    ⟨𝕋'.val.toRingHom.comp (ψ hS).toRingHom, fun _ => rfl⟩
  have h₁ : ∀ ℓ : Nat.Primes, ℓ ∉ S → F₁ (heckeGen ℓ) = F₂ (heckeGen ℓ) := by
    intro ℓ hℓ
    have e1 : F₁ (heckeGen ℓ) = CuspForm.heckeTLin 2 ℓ.prop (not_dvd_level hS hℓ) := by
      rw [hF₁, heckeEvalBarAux_heckeGen]
      exact hΦ ℓ (not_dvd_level hS hℓ)
    have e2 : F₂ (heckeGen ℓ) = CuspForm.heckeTLin 2 ℓ.prop (not_dvd_level hS hℓ) := by
      rw [hF₂, ψ, heckeGen, MvPolynomial.aeval_X, gen_of_not_mem hS hℓ]
    rw [e1, e2]
  have h₂ : ∀ ℓ : Nat.Primes, ℓ ∈ S → F₂ (heckeGen ℓ) = 0 := by
    intro ℓ hℓ
    rw [hF₂, ψ, heckeGen, MvPolynomial.aeval_X, gen_of_mem hS hℓ, ZeroMemClass.coe_zero]

  have h𝔞 : 𝔞 ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝕋') ∈ 𝔞 := htop ▸ Submodule.mem_top
    rw [h𝔞, Ideal.mem_map_iff_of_surjective _ (ψ_surjective hS)] at h1
    obtain ⟨a, haA, ha1⟩ := h1
    have hF0 : Φ (heckeEvalBarAux hcomm (κ S a - 1)) = 0 := by
      rw [← hF₁, map_sub, map_one, comp_κ_eq F₁ F₂ h₁ h₂, hF₂, ha1, Subalgebra.coe_one, sub_self]
    have hker : heckeEvalBarAux hcomm (κ S a - 1) = 0 := (injective_iff_map_eq_zero Φ).1 hΦinj _ hF0
    have hya : (κ S a - 1) • y = 0 := by
      rw [heckeModuleBar_smul_def hcomm, heckeEvalBar_apply, hker, ZeroMemClass.coe_zero,
        LinearMap.zero_apply]
    rw [sub_smul, one_smul, (hmemA a).mp haA, zero_sub, neg_eq_zero] at hya
    exact hy hya
  obtain ⟨𝔪, h𝔪max, h𝔞𝔪⟩ := Ideal.exists_le_maximal 𝔞 h𝔞

  obtain ⟨g, 𝔐, hg, h𝔐max, hev⟩ :=
    CuspForm.exists_isNormalizedEigenform_of_isMaximal_heckeAlgebra N₀ (badSet N₀ p W) 𝔪 h𝔪max
  have hgne : g ≠ 0 := hg.ne_zero

  have hmem𝔪 : ∀ t : HeckeAlg, κ S t = t → t • y = 0 → ψ hS t ∈ 𝔪 := fun t hκ ht =>
    h𝔞𝔪 (Ideal.mem_map_of_mem _ ((hmemA t).mpr (hκ.symm ▸ ht)))
  clear hF₁ hF₂ h₁ h₂ F₁ F₂ hΦ hΦinj Φ

  have hactC : ∀ n : ℤ, ((ψ hS (MvPolynomial.C n) : 𝕋') :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2)) g = (n : ℂ) • g := by
    intro n
    rw [MvPolynomial.algHom_C, Algebra.algebraMap_eq_smul_one, Subalgebra.coe_smul,
      Subalgebra.coe_one, LinearMap.smul_apply, Module.End.one_apply, Int.cast_smul_eq_zsmul]
  have hactX : ∀ {ℓ : Nat.Primes}, ℓ ∉ S → ((ψ hS (heckeGen ℓ) : 𝕋') :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2)) g = ModularFormClass.qCoeff g ℓ • g := by
    intro ℓ hℓS
    rw [ψ, heckeGen, MvPolynomial.aeval_X, gen_of_not_mem hS hℓS]
    exact CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul N₀ g hg ℓ ℓ.prop _
  refine ⟨g, 𝔐, hg, h𝔐max, ?_, ?_⟩
  ·
    have hCp : ψ hS (MvPolynomial.C (p : ℤ)) ∈ 𝔪 := by
      refine hmem𝔪 _ (MvPolynomial.algHom_C _ _) ?_
      rw [heckeModuleBar_C_smul]; exact hpy
    obtain ⟨a, ha, ha𝔪⟩ := hev (ψ hS (MvPolynomial.C (p : ℤ)))
    rw [hactC] at ha
    have hap : ((p : ℤ) : ℂ) = (a : ℂ) := smul_left_injective ℂ hgne ha
    have hap' : (p : integralClosure ℤ ℂ) = a := Subtype.ext (by rw [← hap]; simp)
    exact hap' ▸ ha𝔪 hCp
  ·
    intro ℓ hℓ hgood hℓN hℓp
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ' : Nat.Primes, (ℓ' : ℕ) = ℓ := ⟨⟨ℓ, hℓ⟩, rfl⟩
    have hℓS : ℓ' ∉ S := by
      intro h
      rw [hS] at h
      rcases (Nat.Prime.dvd_mul hℓ).mp h with h1 | h2
      · rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h3 | h4
        · exact hℓN h3
        · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h4)
      · exact hgood (Int.ofNat_dvd_left.mpr h2)
    have hκt : κ S (heckeGen ℓ' - MvPolynomial.C (W.apOfModel ℓ'))
        = heckeGen ℓ' - MvPolynomial.C (W.apOfModel ℓ') := by
      rw [map_sub, heckeGen, κ_X_of_not_mem hℓS, MvPolynomial.algHom_C]; rfl
    have ht𝔪 : ψ hS (heckeGen ℓ' - MvPolynomial.C (W.apOfModel ℓ')) ∈ 𝔪 :=
      hmem𝔪 _ hκt (heig ℓ' hℓS)
    obtain ⟨a, ha, ha𝔪⟩ := hev (ψ hS (heckeGen ℓ' - MvPolynomial.C (W.apOfModel ℓ')))
    rw [map_sub, Subalgebra.coe_sub, LinearMap.sub_apply, hactC, hactX hℓS, ← sub_smul] at ha
    have haval : ModularFormClass.qCoeff g ℓ' - (W.apOfModel ℓ' : ℂ) = (a : ℂ) :=
      smul_left_injective ℂ hgne ha
    refine ⟨a + ((W.apOfModel ℓ' : ℤ) : integralClosure ℤ ℂ), ?_, ?_⟩
    · push_cast [← haval]; ring
    · rw [add_sub_cancel_right]; exact ha𝔪 ht𝔪

end S_WeierstrassCurve_isResiduallyModularOfLevel_of_heckeEigenvector_jZero
end P2MW
export P2MW.S_WeierstrassCurve_isResiduallyModularOfLevel_of_heckeEigenvector_jZero (solution)
