-- Prove2me | solution 1 for WeierstrassCurve.exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fed1e1b0-a6c0-55d5-98c8-b45c1f356705

import Mathlib
import Definitions.Def_ModularCurve_SL2Elementary
import Theorems.Thm_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_ModularCurve_closure_elemSet_eq_top
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace P2M
namespace IgusaSL2

open WeierstrassCurve WeierstrassCurve.Affine Matrix
open scoped MatrixGroups

universe u v

section Action

variable {k : Type v} {Ω : Type v} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω]
  (E : WeierstrassCurve k) [E.IsElliptic] (M : ℕ) [NeZero M]

variable (Ω) in

abbrev Tor : Submodule ℤ (E.baseChange Ω).toAffine.Point :=
  Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point (M : ℤ)

variable {E M}

theorem mem_Tor_iff (P : (E.baseChange Ω).toAffine.Point) : P ∈ Tor Ω E M ↔ M • P = 0 := by
  rw [Tor, Submodule.mem_torsionBy_iff, natCast_zsmul]

theorem map_id' (P : (E.baseChange Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (AlgHom.id k Ω) P = P := by
  cases P <;> rfl

theorem map_symm_map (σ : Ω ≃ₐ[k] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω)
      (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P) = P := by
  rw [Point.map_map, AlgEquiv.symm_comp, map_id']

theorem map_map_symm (σ : Ω ≃ₐ[k] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)
      (WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω) P) = P := by
  rw [Point.map_map, AlgEquiv.comp_symm, map_id']

theorem map_mem_Tor (σ : Ω ≃ₐ[k] Ω) {P : (E.baseChange Ω).toAffine.Point} (hP : P ∈ Tor Ω E M) :
    WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P ∈ Tor Ω E M := by
  rw [mem_Tor_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

variable (E M) in

def actT (σ : Ω ≃ₐ[k] Ω) : Tor Ω E M ≃+ Tor Ω E M where
  toFun P := ⟨WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1, map_mem_Tor σ P.2⟩
  invFun P := ⟨WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω) P.1, by
    have := map_mem_Tor (M := M) σ.symm P.2
    exact this⟩
  left_inv P := by
    apply Subtype.ext
    exact map_symm_map σ P.1
  right_inv P := by
    apply Subtype.ext
    exact map_map_symm σ P.1
  map_add' P Q := by
    apply Subtype.ext
    exact map_add _ P.1 Q.1

@[scoped simp] theorem actT_apply_coe (σ : Ω ≃ₐ[k] Ω) (P : Tor Ω E M) :
    ((actT E M σ P : Tor Ω E M) : (E.baseChange Ω).toAffine.Point) =
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1 := rfl

theorem coe_mul_eq_comp (σ τ : Ω ≃ₐ[k] Ω) :
    ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) = (σ : Ω →ₐ[k] Ω).comp (τ : Ω →ₐ[k] Ω) :=
  AlgHom.ext fun _ => rfl

theorem coe_one_eq_id : ((1 : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) = AlgHom.id k Ω :=
  AlgHom.ext fun _ => rfl

variable (E M) in

def rho (e : ZMod M × ZMod M ≃+ Tor Ω E M) : (Ω ≃ₐ[k] Ω) →* AddAut (ZMod M × ZMod M) where
  toFun σ := (e.trans (actT E M σ)).trans e.symm
  map_one' := by
    ext v
    · show (e.symm (actT E M 1 (e v))).1 = v.1
      have : actT E M 1 (e v) = e v := by
        apply Subtype.ext
        show WeierstrassCurve.Affine.Point.map ((1 : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) (e v).1 = (e v).1
        rw [coe_one_eq_id, map_id']
      rw [this, AddEquiv.symm_apply_apply]
    · show (e.symm (actT E M 1 (e v))).2 = v.2
      have : actT E M 1 (e v) = e v := by
        apply Subtype.ext
        show WeierstrassCurve.Affine.Point.map ((1 : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) (e v).1 = (e v).1
        rw [coe_one_eq_id, map_id']
      rw [this, AddEquiv.symm_apply_apply]
  map_mul' σ τ := by
    have key : ∀ v, actT E M (σ * τ) (e v) = actT E M σ (e (e.symm (actT E M τ (e v)))) := by
      intro v
      rw [AddEquiv.apply_symm_apply]
      apply Subtype.ext
      show WeierstrassCurve.Affine.Point.map ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) (e v).1 =
        WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)
          (WeierstrassCurve.Affine.Point.map (τ : Ω →ₐ[k] Ω) (e v).1)
      rw [Point.map_map, coe_mul_eq_comp]
    ext v
    · show (e.symm (actT E M (σ * τ) (e v))).1 = (e.symm (actT E M σ (e (e.symm (actT E M τ (e v)))))).1
      rw [key]
    · show (e.symm (actT E M (σ * τ) (e v))).2 = (e.symm (actT E M σ (e (e.symm (actT E M τ (e v)))))).2
      rw [key]

theorem rho_apply (e : ZMod M × ZMod M ≃+ Tor Ω E M) (σ : Ω ≃ₐ[k] Ω) (v : ZMod M × ZMod M) :
    rho E M e σ v = e.symm (actT E M σ (e v)) := rfl

theorem addOrderOf_coe_Tor (P : Tor Ω E M) :
    addOrderOf (P : (E.baseChange Ω).toAffine.Point) = addOrderOf P :=
  addOrderOf_injective (Tor Ω E M).subtype.toAddMonoidHom Subtype.val_injective P

end Action

section Basis

variable {k : Type v} {Ω : Type v} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω]
  {E : WeierstrassCurve k} [E.IsElliptic] {M : ℕ} [NeZero M]

def basisHom (P₁ P₂ : Tor Ω E M) : ZMod M × ZMod M →+ Tor Ω E M :=
  (ZMod.lift M ⟨zmultiplesHom (Tor Ω E M) P₁, by
      show ((M : ℕ) : ℤ) • P₁ = 0
      apply Subtype.ext
      show (((M : ℕ) : ℤ) • P₁ : Tor Ω E M).1 = 0
      rw [Submodule.coe_smul_of_tower, natCast_zsmul]
      exact (mem_Tor_iff P₁.1).mp P₁.2⟩).coprod
    (ZMod.lift M ⟨zmultiplesHom (Tor Ω E M) P₂, by
      show ((M : ℕ) : ℤ) • P₂ = 0
      apply Subtype.ext
      show (((M : ℕ) : ℤ) • P₂ : Tor Ω E M).1 = 0
      rw [Submodule.coe_smul_of_tower, natCast_zsmul]
      exact (mem_Tor_iff P₂.1).mp P₂.2⟩)

theorem basisHom_apply_intCast (P₁ P₂ : Tor Ω E M) (a b : ℤ) :
    basisHom P₁ P₂ ((a : ZMod M), (b : ZMod M)) = a • P₁ + b • P₂ := by
  rw [basisHom, AddMonoidHom.coprod_apply, ZMod.lift_coe, ZMod.lift_coe]
  rfl

theorem basisHom_apply (P₁ P₂ : Tor Ω E M) (v : ZMod M × ZMod M) :
    basisHom P₁ P₂ v = (v.1.val : ℤ) • P₁ + (v.2.val : ℤ) • P₂ := by
  have h1 : v = (((v.1.val : ℤ) : ZMod M), ((v.2.val : ℤ) : ZMod M)) := by
    ext <;> simp
  conv_lhs => rw [h1]
  exact basisHom_apply_intCast P₁ P₂ _ _

theorem basisHom_injective (P₁ P₂ : Tor Ω E M)
    (hind : ∀ a b : ℤ, a • (P₁ : (E.baseChange Ω).toAffine.Point) + b • (P₂ : _) = 0 →
      (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) :
    Function.Injective (basisHom P₁ P₂) := by
  intro v w hvw
  have h0 : basisHom P₁ P₂ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  rw [basisHom_apply] at h0
  have h0' : ((v - w).1.val : ℤ) • (P₁ : (E.baseChange Ω).toAffine.Point) +
      ((v - w).2.val : ℤ) • (P₂ : _) = 0 := by
    have := congrArg Subtype.val h0
    simpa using this
  obtain ⟨ha, hb⟩ := hind _ _ h0'
  have h1 : (v - w).1 = 0 := by
    rw [← ZMod.natCast_zmod_val (v - w).1, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ha
  have h2 : (v - w).2 = 0 := by
    rw [← ZMod.natCast_zmod_val (v - w).2, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hb
  have : v - w = 0 := Prod.ext h1 h2
  exact sub_eq_zero.mp this

end Basis

section Group

variable {M : ℕ} [NeZero M]

theorem smul_eq_val_nsmul (a : ZMod M) (v : ZMod M × ZMod M) : a • v = a.val • v := by
  ext <;> simp [nsmul_eq_mul]

theorem map_smul' (h : AddAut (ZMod M × ZMod M)) (a : ZMod M) (v : ZMod M × ZMod M) :
    h (a • v) = a • h v := by
  rw [smul_eq_val_nsmul, map_nsmul, ← smul_eq_val_nsmul]

theorem decomp (v : ZMod M × ZMod M) :
    v = v.1 • ((1, 0) : ZMod M × ZMod M) + v.2 • ((0, 1) : ZMod M × ZMod M) := by
  ext <;> simp

theorem apply_eq (h : AddAut (ZMod M × ZMod M)) (v : ZMod M × ZMod M) :
    h v = v.1 • h (1, 0) + v.2 • h (0, 1) := by
  conv_lhs => rw [decomp v]
  rw [map_add, map_smul', map_smul']

theorem apply_mk (h : AddAut (ZMod M × ZMod M)) (x y : ZMod M) :
    h (x, y) = (x * (h (1, 0)).1 + y * (h (0, 1)).1, x * (h (1, 0)).2 + y * (h (0, 1)).2) := by
  rw [apply_eq]
  ext <;> simp

theorem mul_apply' (f g : AddAut (ZMod M × ZMod M)) (v : ZMod M × ZMod M) :
    (f * g) v = f (g v) := rfl

theorem intCast_smul (n : ℤ) (v : ZMod M × ZMod M) : (n : ZMod M) • v = n • v :=
  Int.cast_smul_eq_zsmul (ZMod M) n v

theorem natCast_nsmul_eq_zero (v : ZMod M × ZMod M) : M • v = 0 := by
  ext <;> simp [nsmul_eq_mul]

theorem addOrderOf_one_zero : addOrderOf ((1, 0) : ZMod M × ZMod M) = M := by
  rw [Prod.addOrderOf]
  simp [ZMod.addOrderOf_one]

theorem addOrderOf_zero_one : addOrderOf ((0, 1) : ZMod M × ZMod M) = M := by
  rw [Prod.addOrderOf]
  simp [ZMod.addOrderOf_one]

theorem isUnit_of_addOrderOf_smul (c : ZMod M) (v : ZMod M × ZMod M)
    (h : addOrderOf (c • v) = M) : IsUnit c := by
  have hM : M ≠ 0 := NeZero.ne M
  rw [← ZMod.natCast_zmod_val c, ZMod.isUnit_iff_coprime]
  by_contra hcop
  set g := Nat.gcd c.val M with hg
  have hg1 : g ≠ 1 := hcop
  have hgM : g ∣ M := Nat.gcd_dvd_right _ _
  have hgc : g ∣ c.val := Nat.gcd_dvd_left _ _
  have hgpos : 0 < g := Nat.pos_of_ne_zero (by
    intro h0
    rw [hg, Nat.gcd_eq_zero_iff] at h0
    exact hM h0.2)
  obtain ⟨m, hm⟩ := hgM
  obtain ⟨d, hd⟩ := hgc
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm; exact absurd hm hM
    · exact h0
  have hmlt : m < M := by
    have h2 : 2 ≤ g := by omega
    calc m < 2 * m := by omega
      _ ≤ g * m := Nat.mul_le_mul_right m h2
      _ = M := hm.symm

  have hkill : m • (c • v) = 0 := by
    rw [smul_eq_val_nsmul, ← mul_nsmul', hd, show m * (g * d) = d * (g * m) by ring, ← hm,
      mul_nsmul', natCast_nsmul_eq_zero, nsmul_zero]
  have hle : addOrderOf (c • v) ≤ m := addOrderOf_le_of_nsmul_eq_zero hmpos hkill
  omega

variable (H : Subgroup (AddAut (ZMod M × ZMod M)))

def R (x : ZMod M × ZMod M) : Prop := ∃ g ∈ H, g (1, 0) = x

variable {H}

theorem R_one : R H (1, 0) := ⟨1, one_mem H, rfl⟩

theorem R_apply {x : ZMod M × ZMod M} (hx : R H x) {g : AddAut (ZMod M × ZMod M)} (hg : g ∈ H) :
    R H (g x) := by
  obtain ⟨g', hg', rfl⟩ := hx
  exact ⟨g * g', mul_mem hg hg', rfl⟩

theorem exists_of_R {v w : ZMod M × ZMod M} (hv : R H v) (hw : R H w) : ∃ h ∈ H, h v = w := by
  obtain ⟨g, hg, rfl⟩ := hv
  obtain ⟨g', hg', rfl⟩ := hw
  refine ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), ?_⟩
  rw [mul_apply', AddAut.inv_def', AddEquiv.symm_apply_apply]

structure Frame (H : Subgroup (AddAut (ZMod M × ZMod M))) where
  t : AddAut (ZMod M × ZMod M)
  ht : t ∈ H
  e : ZMod M
  he : e = 1 ∨ e = -1
  t_apply : ∀ x y : ZMod M, t (x, y) = (e * (x + y), e * y)
  ℓ : AddAut (ZMod M × ZMod M)
  hℓ : ℓ ∈ H
  z : ZMod M
  hz : IsUnit z
  ℓ_apply : ∀ x y : ZMod M, ℓ (x, y) = (e * x, e * (z * x + y))

theorem exists_frame
    (htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w)
    (ht : ∃ t ∈ H, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      t (1, 0) = ε • ((1, 0) : ZMod M × ZMod M) ∧ t (0, 1) = ε • ((1, 1) : ZMod M × ZMod M)) :
    Nonempty (Frame H) := by
  obtain ⟨t, htH, ε, hε, ht1, ht2⟩ := ht
  set e : ZMod M := (ε : ZMod M) with he_def
  have he : e = 1 ∨ e = -1 := by
    rcases hε with h | h
    · left; rw [he_def, h, Int.cast_one]
    · right; rw [he_def, h, Int.cast_neg, Int.cast_one]
  have ht1' : t (1, 0) = (e, 0) := by
    rw [ht1, ← intCast_smul]; ext <;> simp [he_def]
  have ht2' : t (0, 1) = (e, e) := by
    rw [ht2, ← intCast_smul]; ext <;> simp [he_def]
  have t_apply : ∀ x y : ZMod M, t (x, y) = (e * (x + y), e * y) := by
    intro x y
    rw [apply_mk, ht1', ht2']
    ext <;> simp <;> ring

  obtain ⟨h₀, hh₀, n₀, hn₀⟩ := htrans (1, 0) (0, 1) addOrderOf_one_zero addOrderOf_zero_one
  set a : ZMod M := (n₀ : ZMod M) with ha_def
  have h01 : h₀ (1, 0) = (0, a) := by
    rw [hn₀, ← intCast_smul]; ext <;> simp [ha_def]
  set β : ZMod M := (h₀ (0, 1)).1 with hβ
  set γ : ZMod M := (h₀ (0, 1)).2 with hγ
  have h02 : h₀ (0, 1) = (β, γ) := Prod.ext rfl rfl
  have h0_apply : ∀ x y : ZMod M, h₀ (x, y) = (y * β, x * a + y * γ) := by
    intro x y
    rw [apply_mk, h01, h02]
    ext <;> simp

  set x₀ := (h₀.symm (1, 0)).1
  set y₀ := (h₀.symm (1, 0)).2
  set x₁ := (h₀.symm (0, 1)).1
  set y₁ := (h₀.symm (0, 1)).2
  have hs1 : h₀.symm (1, 0) = (x₀, y₀) := Prod.ext rfl rfl
  have hs2 : h₀.symm (0, 1) = (x₁, y₁) := Prod.ext rfl rfl
  have E1 : ((1, 0) : ZMod M × ZMod M) = (y₀ * β, x₀ * a + y₀ * γ) := by
    rw [← h0_apply, ← hs1, AddEquiv.apply_symm_apply]
  have E2 : ((0, 1) : ZMod M × ZMod M) = (y₁ * β, x₁ * a + y₁ * γ) := by
    rw [← h0_apply, ← hs2, AddEquiv.apply_symm_apply]
  have hy₀β : y₀ * β = 1 := ((Prod.ext_iff.mp E1).1).symm
  have hx₀ : x₀ * a + y₀ * γ = 0 := ((Prod.ext_iff.mp E1).2).symm
  have hy₁β : y₁ * β = 0 := ((Prod.ext_iff.mp E2).1).symm
  have hx₁' : x₁ * a + y₁ * γ = 1 := ((Prod.ext_iff.mp E2).2).symm
  have hy₁ : y₁ = 0 := by
    calc y₁ = y₁ * (y₀ * β) := by rw [hy₀β, mul_one]
      _ = y₀ * (y₁ * β) := by ring
      _ = 0 := by rw [hy₁β, mul_zero]
  have hx₁ : x₁ * a = 1 := by rw [hy₁, zero_mul, add_zero] at hx₁'; exact hx₁'

  set ℓ := h₀ * t * h₀⁻¹ with hℓ_def
  have hℓH : ℓ ∈ H := mul_mem (mul_mem hh₀ htH) (inv_mem hh₀)
  have hℓ1 : ℓ (1, 0) = (e, e * (y₀ * a)) := by
    rw [hℓ_def, mul_apply', mul_apply', AddAut.inv_def', hs1, t_apply, h0_apply]
    ext
    · show e * y₀ * β = e
      rw [mul_assoc, hy₀β, mul_one]
    · show e * (x₀ + y₀) * a + e * y₀ * γ = e * (y₀ * a)
      linear_combination e * hx₀
  have hℓ2 : ℓ (0, 1) = (0, e) := by
    rw [hℓ_def, mul_apply', mul_apply', AddAut.inv_def', hs2, t_apply, h0_apply, hy₁]
    ext
    · show e * 0 * β = 0
      ring
    · show e * (x₁ + 0) * a + e * 0 * γ = e
      linear_combination e * hx₁
  have ℓ_apply : ∀ x y : ZMod M, ℓ (x, y) = (e * x, e * (y₀ * a * x + y)) := by
    intro x y
    rw [apply_mk, hℓ1, hℓ2]
    ext <;> simp <;> ring
  have hz : IsUnit (y₀ * a) :=
    (IsUnit.of_mul_eq_one β hy₀β).mul (IsUnit.of_mul_eq_one_right x₁ hx₁)
  exact ⟨⟨t, htH, e, he, t_apply, ℓ, hℓH, y₀ * a, hz, ℓ_apply⟩⟩

namespace Frame

variable (Fr : Frame H)

theorem e_sq : Fr.e * Fr.e = 1 := by
  rcases Fr.he with h | h <;> rw [h] <;> ring

theorem e_pow_two_mul (n : ℕ) : Fr.e ^ (2 * n) = 1 := by
  rw [pow_mul, sq, e_sq, one_pow]

theorem t_pow_apply (n : ℕ) (x y : ZMod M) :
    (Fr.t ^ n) (x, y) = (Fr.e ^ n * (x + n * y), Fr.e ^ n * y) := by
  induction n generalizing x y with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, mul_apply', Fr.t_apply, ih]
    ext <;> push_cast <;> ring

def kk : ℕ := (-(Fr.z⁻¹) : ZMod M).val

theorem kk_mul_z : (Fr.kk : ZMod M) * Fr.z = -1 := by
  rw [kk, ZMod.natCast_zmod_val, neg_mul, ZMod.inv_mul_of_unit _ Fr.hz]

def gS : AddAut (ZMod M × ZMod M) := Fr.t ^ Fr.kk * Fr.ℓ * Fr.t ^ Fr.kk

theorem gS_mem : Fr.gS ∈ H :=
  mul_mem (mul_mem (pow_mem Fr.ht _) Fr.hℓ) (pow_mem Fr.ht _)

theorem gS_apply_one_zero : Fr.gS (1, 0) = (0, Fr.e * Fr.z) := by
  rw [gS, mul_apply', mul_apply', t_pow_apply, Fr.ℓ_apply, t_pow_apply]
  have h1 := Fr.kk_mul_z
  have h2 := Fr.e_pow_two_mul Fr.kk
  ext
  · show Fr.e ^ Fr.kk * (Fr.e * (Fr.e ^ Fr.kk * (1 + Fr.kk * 0)) +
        Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (1 + Fr.kk * 0)) + Fr.e ^ Fr.kk * 0))) = 0
    have : Fr.e ^ Fr.kk * (Fr.e * (Fr.e ^ Fr.kk * (1 + Fr.kk * 0)) +
        Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (1 + Fr.kk * 0)) + Fr.e ^ Fr.kk * 0))) =
        Fr.e ^ (2 * Fr.kk) * Fr.e * (1 + Fr.kk * Fr.z) := by ring
    rw [this, h1]; ring
  · show Fr.e ^ Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (1 + ↑Fr.kk * 0)) + Fr.e ^ Fr.kk * 0)) =
        Fr.e * Fr.z
    have : Fr.e ^ Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (1 + ↑Fr.kk * 0)) + Fr.e ^ Fr.kk * 0)) =
        Fr.e ^ (2 * Fr.kk) * (Fr.e * Fr.z) := by ring
    rw [this, h2, one_mul]

theorem gS_apply_zero_one : Fr.gS (0, 1) = (Fr.e * Fr.kk, 0) := by
  rw [gS, mul_apply', mul_apply', t_pow_apply, Fr.ℓ_apply, t_pow_apply]
  have h1 := Fr.kk_mul_z
  have h2 := Fr.e_pow_two_mul Fr.kk
  ext
  · show Fr.e ^ Fr.kk * (Fr.e * (Fr.e ^ Fr.kk * (0 + Fr.kk * 1)) +
        Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (0 + Fr.kk * 1)) + Fr.e ^ Fr.kk * 1))) =
        Fr.e * Fr.kk
    have : Fr.e ^ Fr.kk * (Fr.e * (Fr.e ^ Fr.kk * (0 + Fr.kk * 1)) +
        Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (0 + Fr.kk * 1)) + Fr.e ^ Fr.kk * 1))) =
        Fr.e ^ (2 * Fr.kk) * Fr.e * Fr.kk * (1 + (Fr.kk * Fr.z + 1)) := by ring
    rw [this, h1, h2]; ring
  · show Fr.e ^ Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (0 + ↑Fr.kk * 1)) + Fr.e ^ Fr.kk * 1)) = 0
    have : Fr.e ^ Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (0 + ↑Fr.kk * 1)) + Fr.e ^ Fr.kk * 1)) =
        Fr.e ^ (2 * Fr.kk) * Fr.e * (Fr.kk * Fr.z + 1) := by ring
    rw [this, h1]; ring

theorem gS_apply (x y : ZMod M) : Fr.gS (x, y) = (Fr.e * Fr.kk * y, Fr.e * Fr.z * x) := by
  rw [apply_mk, gS_apply_one_zero, gS_apply_zero_one]
  ext <;> simp <;> ring

theorem gS_sq_apply (v : ZMod M × ZMod M) : (Fr.gS * Fr.gS) v = -v := by
  obtain ⟨x, y⟩ := v
  rw [mul_apply', gS_apply, gS_apply]
  have h1 := Fr.kk_mul_z
  have h2 := Fr.e_sq
  ext
  · show Fr.e * Fr.kk * (Fr.e * Fr.z * x) = -x
    have : Fr.e * Fr.kk * (Fr.e * Fr.z * x) = (Fr.e * Fr.e) * (Fr.kk * Fr.z) * x := by ring
    rw [this, h1, h2]; ring
  · show Fr.e * Fr.z * (Fr.e * Fr.kk * y) = -y
    have : Fr.e * Fr.z * (Fr.e * Fr.kk * y) = (Fr.e * Fr.e) * (Fr.kk * Fr.z) * y := by ring
    rw [this, h1, h2]; ring

end Frame

def Φaux (g : SL(2, ZMod M)) : ZMod M × ZMod M →+ ZMod M × ZMod M where
  toFun v := (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2)
  map_zero' := by ext <;> simp
  map_add' v w := by ext <;> simp <;> ring

theorem Φaux_apply (g : SL(2, ZMod M)) (v : ZMod M × ZMod M) :
    Φaux g v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) := rfl

theorem Φaux_mul (g h : SL(2, ZMod M)) (v : ZMod M × ZMod M) : Φaux (g * h) v = Φaux g (Φaux h v) := by
  rw [Φaux_apply, Φaux_apply, Φaux_apply]
  have e : ∀ i j, (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := by
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp only [e] <;> ring

theorem Φaux_one (v : ZMod M × ZMod M) : Φaux (1 : SL(2, ZMod M)) v = v := by
  rw [Φaux_apply]
  ext <;> simp

def Φ : SL(2, ZMod M) →* AddAut (ZMod M × ZMod M) where
  toFun g :=
    { toFun := Φaux g
      invFun := Φaux g⁻¹
      left_inv := fun v => by
        show Φaux g⁻¹ (Φaux g v) = v
        rw [← Φaux_mul, inv_mul_cancel, Φaux_one]
      right_inv := fun v => by
        show Φaux g (Φaux g⁻¹ v) = v
        rw [← Φaux_mul, mul_inv_cancel, Φaux_one]
      map_add' := fun v w => map_add _ v w }
  map_one' := by
    ext v
    · show (Φaux 1 v).1 = v.1
      rw [Φaux_one]
    · show (Φaux 1 v).2 = v.2
      rw [Φaux_one]
  map_mul' g h := by
    ext v
    · show (Φaux (g * h) v).1 = (Φaux g (Φaux h v)).1
      rw [Φaux_mul]
    · show (Φaux (g * h) v).2 = (Φaux g (Φaux h v)).2
      rw [Φaux_mul]

theorem Φ_apply (g : SL(2, ZMod M)) (v : ZMod M × ZMod M) :
    Φ g v = (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2) := rfl

theorem Φ_upperElem (b : ZMod M) (x y : ZMod M) : Φ (ModularCurve.upperElem b) (x, y) = (x + b * y, y) := by
  rw [Φ_apply]
  ext <;> simp [ModularCurve.upperElem]

theorem Φ_lowerElem (c : ZMod M) (x y : ZMod M) : Φ (ModularCurve.lowerElem c) (x, y) = (x, c * x + y) := by
  rw [Φ_apply]
  ext <;> simp [ModularCurve.lowerElem]

def toMat (f : AddAut (ZMod M × ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  !![(f (1, 0)).1, (f (0, 1)).1; (f (1, 0)).2, (f (0, 1)).2]

@[scoped simp] theorem toMat_00 (f : AddAut (ZMod M × ZMod M)) : toMat f 0 0 = (f (1, 0)).1 := rfl
@[scoped simp] theorem toMat_01 (f : AddAut (ZMod M × ZMod M)) : toMat f 0 1 = (f (0, 1)).1 := rfl
@[scoped simp] theorem toMat_10 (f : AddAut (ZMod M × ZMod M)) : toMat f 1 0 = (f (1, 0)).2 := rfl
@[scoped simp] theorem toMat_11 (f : AddAut (ZMod M × ZMod M)) : toMat f 1 1 = (f (0, 1)).2 := rfl

theorem apply_eq_toMat (f : AddAut (ZMod M × ZMod M)) (x y : ZMod M) :
    f (x, y) = (toMat f 0 0 * x + toMat f 0 1 * y, toMat f 1 0 * x + toMat f 1 1 * y) := by
  rw [apply_mk, toMat_00, toMat_01, toMat_10, toMat_11]
  ext <;> ring

theorem toMat_mul (f g : AddAut (ZMod M × ZMod M)) : toMat (f * g) = toMat f * toMat g := by
  have h10 : (f * g) (1, 0) = f (g (1, 0)) := rfl
  have h01 : (f * g) (0, 1) = f (g (0, 1)) := rfl
  have e1 : f (g (1, 0)) = (toMat f 0 0 * (g (1, 0)).1 + toMat f 0 1 * (g (1, 0)).2,
      toMat f 1 0 * (g (1, 0)).1 + toMat f 1 1 * (g (1, 0)).2) := apply_eq_toMat f _ _
  have e2 : f (g (0, 1)) = (toMat f 0 0 * (g (0, 1)).1 + toMat f 0 1 * (g (0, 1)).2,
      toMat f 1 0 * (g (0, 1)).1 + toMat f 1 1 * (g (0, 1)).2) := apply_eq_toMat f _ _
  rw [toMat_00, toMat_01, toMat_10, toMat_11] at e1 e2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, Matrix.mul_apply, Fin.sum_univ_two, h10, h01, e1, e2]

theorem toMat_one : toMat (1 : AddAut (ZMod M × ZMod M)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def detA (f : AddAut (ZMod M × ZMod M)) : ZMod M := (toMat f).det

theorem detA_mul (f g : AddAut (ZMod M × ZMod M)) : detA (f * g) = detA f * detA g := by
  rw [detA, toMat_mul, Matrix.det_mul]; rfl

theorem detA_one : detA (1 : AddAut (ZMod M × ZMod M)) = 1 := by
  rw [detA, toMat_one, Matrix.det_one]

theorem detA_conj (m f : AddAut (ZMod M × ZMod M)) : detA (m * f * m⁻¹) = detA f := by
  have h : detA m * detA m⁻¹ = 1 := by rw [← detA_mul, mul_inv_cancel, detA_one]
  rw [detA_mul, detA_mul, mul_comm (detA m) (detA f), mul_assoc, h, mul_one]

theorem toMat_Φ (g : SL(2, ZMod M)) : toMat (Φ g) = (g : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Φ_apply]

theorem detA_Φ (g : SL(2, ZMod M)) : detA (Φ g) = 1 := by
  rw [detA, toMat_Φ, g.prop]

theorem eq_Φ_of_detA_eq_one (f : AddAut (ZMod M × ZMod M)) (hf : detA f = 1) :
    f = Φ ⟨toMat f, hf⟩ := by
  ext v <;> obtain ⟨x, y⟩ := v
  · show (f (x, y)).1 = (Φ ⟨toMat f, hf⟩ (x, y)).1
    rw [apply_eq_toMat, Φ_apply]
  · show (f (x, y)).2 = (Φ ⟨toMat f, hf⟩ (x, y)).2
    rw [apply_eq_toMat, Φ_apply]

theorem Φ_mem (Fr : Frame H) (g : SL(2, ZMod M)) : Φ g ∈ H := by

  set n : AddAut (ZMod M × ZMod M) := Fr.gS * Fr.gS with hn
  have hnH : n ∈ H := mul_mem Fr.gS_mem Fr.gS_mem
  have hn_apply : ∀ v, n v = -v := Fr.gS_sq_apply

  have key : ∀ (f g' : AddAut (ZMod M × ZMod M)), g' ∈ H →
      (∀ v, g' v = (Fr.e * (f v).1, Fr.e * (f v).2)) → f ∈ H := by
    intro f g' hg' hfg
    rcases Fr.he with h1 | h1
    · have : f = g' := by
        ext v
        · rw [hfg, h1]; simp
        · rw [hfg, h1]; simp
      rw [this]; exact hg'
    · have : f = n * g' := by
        ext v
        · show (f v).1 = (n (g' v)).1
          rw [hn_apply, hfg, h1]; simp
        · show (f v).2 = (n (g' v)).2
          rw [hn_apply, hfg, h1]; simp
      rw [this]; exact mul_mem hnH hg'

  have hT : Φ (ModularCurve.upperElem (1 : ZMod M)) ∈ H := by
    apply key _ Fr.t Fr.ht
    rintro ⟨x, y⟩
    rw [Fr.t_apply, Φ_upperElem, one_mul]
  have hL : Φ (ModularCurve.lowerElem Fr.z) ∈ H := by
    apply key _ Fr.ℓ Fr.hℓ
    rintro ⟨x, y⟩
    rw [Fr.ℓ_apply, Φ_lowerElem]

  have hupper : ∀ b : ZMod M, Φ (ModularCurve.upperElem b) ∈ H := by
    intro b
    have : ModularCurve.upperElem b = ModularCurve.upperElem (1 : ZMod M) ^ b.val := by
      rw [ModularCurve.upperElem_pow, mul_one, ZMod.natCast_zmod_val]
    rw [this, map_pow]
    exact pow_mem hT _
  have hlower : ∀ c : ZMod M, Φ (ModularCurve.lowerElem c) ∈ H := by
    intro c
    have : ModularCurve.lowerElem c = ModularCurve.lowerElem Fr.z ^ (c * Fr.z⁻¹).val := by
      rw [ModularCurve.lowerElem_pow, ZMod.natCast_zmod_val, mul_assoc, ZMod.inv_mul_of_unit _ Fr.hz, mul_one]
    rw [this, map_pow]
    exact pow_mem hL _

  have hcl : (Subgroup.closure (ModularCurve.elemSet (ZMod M))).map Φ ≤ H := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with ⟨b, rfl⟩ | ⟨c, rfl⟩
    · exact hupper b
    · exact hlower c
  rw [ModularCurve.closure_elemSet_eq_top] at hcl
  exact hcl ⟨g, Subgroup.mem_top g, rfl⟩

theorem mem_of_detA_eq_one (Fr : Frame H) (f : AddAut (ZMod M × ZMod M)) (hf : detA f = 1) : f ∈ H := by
  rw [eq_Φ_of_detA_eq_one f hf]
  exact Φ_mem Fr _

end Group

theorem main
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)
    (P₁ P₂ : (E.baseChange Ω).toAffine.Point) (hP₁ : M • P₁ = 0) (hP₂ : M • P₂ = 0)
    (hind : ∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)
    (a b c d : ℤ) (hdet : (M : ℤ) ∣ a * d - b * c - 1) :
    ∃ σ : Ω ≃ₐ[k] Ω,
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₁ = a • P₁ + c • P₂ ∧
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₂ = b • P₁ + d • P₂ := by

  have hMΩ : (M : Ω) ≠ 0 := by
    intro h
    apply hM
    have : algebraMap K Ω (M : K) = 0 := by rw [map_natCast, h]
    exact (algebraMap K Ω).injective (by rw [this, map_zero])
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k

  obtain ⟨e₀⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (K := Ω) E (n := M) hMΩ
  have hcardT : Nat.card (Tor Ω E M) = M ^ 2 := by
    rw [← Nat.card_congr e₀.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  haveI : Finite (Tor Ω E M) := Nat.finite_of_card_ne_zero (by
    rw [hcardT]; exact pow_ne_zero 2 (NeZero.ne M))

  have mkE : ∀ (T₁ T₂ : Tor Ω E M),
      (∀ a b : ℤ, a • (T₁ : (E.baseChange Ω).toAffine.Point) + b • (T₂ : _) = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) →
      ∃ e : ZMod M × ZMod M ≃+ Tor Ω E M, ∀ v, e v = basisHom T₁ T₂ v := by
    intro T₁ T₂ hi
    have hinj : Function.Injective (basisHom T₁ T₂) := basisHom_injective T₁ T₂ hi
    have hbij : Function.Bijective (basisHom T₁ T₂) := by
      apply hinj.bijective_of_nat_card_le
      rw [hcardT, Nat.card_prod, Nat.card_zmod, sq]
    exact ⟨AddEquiv.ofBijective (basisHom T₁ T₂) hbij, fun v => rfl⟩

  obtain ⟨B₁, B₂, σ₀, ε, hB₁, hB₂, hBind, hε, hσ₁, hσ₂⟩ :=
    WeierstrassCurve.exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
      K M hM k Ω E hE hgen
  set T₁ : Tor Ω E M := ⟨B₁, (mem_Tor_iff B₁).mpr hB₁⟩ with hT₁
  set T₂ : Tor Ω E M := ⟨B₂, (mem_Tor_iff B₂).mpr hB₂⟩ with hT₂
  obtain ⟨e, he_apply⟩ := mkE T₁ T₂ hBind
  have he10 : e (1, 0) = T₁ := by
    rw [he_apply, show ((1, 0) : ZMod M × ZMod M) = (((1 : ℤ) : ZMod M), ((0 : ℤ) : ZMod M)) by simp,
      basisHom_apply_intCast, one_zsmul, zero_zsmul, add_zero]
  have he01 : e (0, 1) = T₂ := by
    rw [he_apply, show ((0, 1) : ZMod M × ZMod M) = (((0 : ℤ) : ZMod M), ((1 : ℤ) : ZMod M)) by simp,
      basisHom_apply_intCast, one_zsmul, zero_zsmul, zero_add]
  have he11 : e (1, 1) = T₁ + T₂ := by
    rw [he_apply, show ((1, 1) : ZMod M × ZMod M) = (((1 : ℤ) : ZMod M), ((1 : ℤ) : ZMod M)) by simp,
      basisHom_apply_intCast, one_zsmul, one_zsmul]
  set H : Subgroup (AddAut (ZMod M × ZMod M)) := (rho E M e).range with hH

  have htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w := by
    intro v w hv hw
    have hv' : addOrderOf ((e v : Tor Ω E M) : (E.baseChange Ω).toAffine.Point) = M := by
      rw [addOrderOf_coe_Tor, AddEquiv.addOrderOf_eq, hv]
    have hw' : addOrderOf ((e w : Tor Ω E M) : (E.baseChange Ω).toAffine.Point) = M := by
      rw [addOrderOf_coe_Tor, AddEquiv.addOrderOf_eq, hw]
    obtain ⟨σ, hσ⟩ := WeierstrassCurve.exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j
      K M hM k Ω E hE hgen _ _ hv' hw'
    refine ⟨rho E M e σ, ⟨σ, rfl⟩, 1, ?_⟩
    rw [rho_apply, one_zsmul]
    have : actT E M σ (e v) = e w := by
      apply Subtype.ext
      rw [actT_apply_coe]
      exact hσ.symm
    rw [this, AddEquiv.symm_apply_apply]

  have ht : ∃ t ∈ H, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      t (1, 0) = ε • ((1, 0) : ZMod M × ZMod M) ∧ t (0, 1) = ε • ((1, 1) : ZMod M × ZMod M) := by
    refine ⟨rho E M e σ₀, ⟨σ₀, rfl⟩, ε, hε, ?_, ?_⟩
    · rw [rho_apply, he10]
      have : actT E M σ₀ T₁ = ε • T₁ := by
        apply Subtype.ext
        rw [actT_apply_coe, Submodule.coe_smul_of_tower]
        exact hσ₁
      rw [this, map_zsmul, ← he10, AddEquiv.symm_apply_apply]
    · rw [rho_apply, he01]
      have : actT E M σ₀ T₂ = ε • (T₁ + T₂) := by
        apply Subtype.ext
        rw [actT_apply_coe, Submodule.coe_smul_of_tower]
        exact hσ₂
      rw [this, map_zsmul, ← he11, AddEquiv.symm_apply_apply]
  obtain ⟨Fr⟩ := exists_frame (H := H) htrans ht

  set U₁ : Tor Ω E M := ⟨P₁, (mem_Tor_iff P₁).mpr hP₁⟩ with hU₁
  set U₂ : Tor Ω E M := ⟨P₂, (mem_Tor_iff P₂).mpr hP₂⟩ with hU₂
  obtain ⟨eP, heP_apply⟩ := mkE U₁ U₂ hind
  have heP10 : eP (1, 0) = U₁ := by
    rw [heP_apply, show ((1, 0) : ZMod M × ZMod M) = (((1 : ℤ) : ZMod M), ((0 : ℤ) : ZMod M)) by simp,
      basisHom_apply_intCast, one_zsmul, zero_zsmul, add_zero]
  have heP01 : eP (0, 1) = U₂ := by
    rw [heP_apply, show ((0, 1) : ZMod M × ZMod M) = (((0 : ℤ) : ZMod M), ((1 : ℤ) : ZMod M)) by simp,
      basisHom_apply_intCast, one_zsmul, zero_zsmul, zero_add]
  have hdet' : ((a : ZMod M) * (d : ZMod M) - (b : ZMod M) * (c : ZMod M)) = 1 := by
    have h0 : (((a * d - b * c - 1 : ℤ)) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).2 hdet
    push_cast at h0
    linear_combination h0
  set g : SL(2, ZMod M) := ⟨!![(a : ZMod M), (b : ZMod M); (c : ZMod M), (d : ZMod M)], by
    rw [Matrix.det_fin_two_of]; exact hdet'⟩ with hg
  have hg10 : Φ g (1, 0) = ((a : ZMod M), (c : ZMod M)) := by
    rw [Φ_apply]; ext <;> simp [hg]
  have hg01 : Φ g (0, 1) = ((b : ZMod M), (d : ZMod M)) := by
    rw [Φ_apply]; ext <;> simp [hg]

  set m : AddAut (ZMod M × ZMod M) := (eP.trans e.symm : ZMod M × ZMod M ≃+ ZMod M × ZMod M) with hm
  set φ : AddAut (ZMod M × ZMod M) := m * Φ g * m⁻¹ with hφ
  have hφdet : detA φ = 1 := by rw [hφ, detA_conj, detA_Φ]
  obtain ⟨σ, hσ⟩ := mem_of_detA_eq_one Fr φ hφdet

  have hφ_apply : ∀ v, φ v = e.symm (eP (Φ g (eP.symm (e v)))) := fun v => rfl
  have hact : ∀ u : Tor Ω E M, actT E M σ u = eP (Φ g (eP.symm u)) := by
    intro u
    have h1 : rho E M e σ (e.symm u) = φ (e.symm u) := by rw [hσ]
    rw [rho_apply, hφ_apply, AddEquiv.apply_symm_apply] at h1
    exact e.symm.injective h1
  have hcomb : ∀ p q : ℤ, eP ((p : ZMod M), (q : ZMod M)) = p • U₁ + q • U₂ := by
    intro p q; rw [heP_apply, basisHom_apply_intCast]
  refine ⟨σ, ?_, ?_⟩
  · have h1 := hact U₁
    rw [← heP10, AddEquiv.symm_apply_apply, hg10, hcomb, heP10] at h1
    have := congrArg Subtype.val h1
    simpa only [actT_apply_coe, Submodule.coe_add, Submodule.coe_smul_of_tower] using this
  · have h1 := hact U₂
    rw [← heP01, AddEquiv.symm_apply_apply, hg01, hcomb, heP01] at h1
    have := congrArg Subtype.val h1
    simpa only [actT_apply_coe, Submodule.coe_add, Submodule.coe_smul_of_tower] using this

end P2M.IgusaSL2
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j.P2M P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j.P2M.IgusaSL2"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j.P2M"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j.P2M P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j.P2M.IgusaSL2"

open WeierstrassCurve WeierstrassCurve.Affine

universe u v in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)
    (P₁ P₂ : (E.baseChange Ω).toAffine.Point) (hP₁ : M • P₁ = 0) (hP₂ : M • P₂ = 0)
    (hind : ∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)
    (a b c d : ℤ) (hdet : (M : ℤ) ∣ a * d - b * c - 1) :
    ∃ σ : Ω ≃ₐ[k] Ω,
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₁ = a • P₁ + c • P₂ ∧
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₂ = b • P₁ + d • P₂ :=
  P2M.IgusaSL2.main K M hM k Ω E hE hgen P₁ P₂ hP₁ hP₂ hind a b c d hdet

end S_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j
end P2MW
export P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_zsmul_add_zsmul_of_transcendental_j (solution)
