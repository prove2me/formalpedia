-- Prove2me | solution 1 for WeierstrassCurve.exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/da320d80-fba0-5fc4-a47b-4a8cb51fb670

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem
import Theorems.Thm_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
import Theorems.Thm_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply"
p2m_attr_erase "simp" "ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace P2MKcIgusaMonodromy

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

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

section Irred

variable (K : Type u) [Field K] {k : Type v} [Field k] [Algebra K k]

theorem exists_algEquiv_ratFunc {x : k} (hx : Transcendental K x)
    (hgen : IntermediateField.adjoin K ({x} : Set k) = ⊤) :
    ∃ φ : RatFunc K ≃ₐ[K] k, φ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = x := by
  have hinj : Function.Injective (Polynomial.aeval (R := K) x) := transcendental_iff_injective.mp hx
  have hφ : nonZeroDivisors (Polynomial K) ≤
      Submonoid.comap (Polynomial.aeval (R := K) x) (nonZeroDivisors k) := by
    intro p hp
    rw [Submonoid.mem_comap]
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    have : p = 0 := hinj (by rw [h0, map_zero])
    exact nonZeroDivisors.ne_zero hp this
  set ψ : RatFunc K →ₐ[K] k := RatFunc.liftAlgHom (Polynomial.aeval x) hφ with hψ
  have hψX : ψ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = x := by
    have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval (R := K) x) hφ Polynomial.X 1
    rw [map_one, div_one, map_one, div_one, Polynomial.aeval_X] at h
    exact h
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : y ∈ (⊤ : IntermediateField K k) := IntermediateField.mem_top
    rw [← hgen] at hy
    have hle : IntermediateField.adjoin K ({x} : Set k) ≤ ψ.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact AlgHom.mem_fieldRange.mpr ⟨_, hψX⟩
    exact AlgHom.mem_fieldRange.mp (hle hy)
  exact ⟨AlgEquiv.ofBijective ψ ⟨ψ.toRingHom.injective, hsurj⟩, hψX⟩

theorem irreducible_fibre {M : ℕ} [NeZero M] (data : ModularCurve.ModularPolynomialData M)
    (hM : (M : K) ≠ 0) {x : k} (hx : Transcendental K x)
    (hgen : IntermediateField.adjoin K ({x} : Set k) = ⊤) :
    Irreducible (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) x)) := by
  obtain ⟨φ, hφX⟩ := exists_algEquiv_ratFunc K hx hgen
  have hirr := data.irreducible_map_ratFunc_of_natCast_ne_zero K M hM
  rw [Polynomial.map_map] at hirr
  rw [← MulEquiv.irreducible_iff (Polynomial.mapEquiv (φ : RatFunc K ≃+* k))] at hirr
  convert hirr using 1
  rw [Polynomial.mapEquiv_apply, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp only [eq_intCast, map_intCast]
  · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.coe_mapRingHom, Polynomial.map_X, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv]
    exact hφX.symm

end Irred

section Lines

variable (K : Type u) [Field K] (M : ℕ) [NeZero M] (hMK : (M : K) ≠ 0)
  (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra k Ω]
  [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
  (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)

include hMK hE hgen in

theorem exists_map_mem_zmultiples
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2)
    (P Q : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = M) (hQ : addOrderOf Q = M) :
    ∃ (σ : Ω ≃ₐ[k] Ω) (n : ℤ),
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P = n • Q := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData M
  have hMk : (M : k) ≠ 0 := by
    intro h
    apply hMK
    have : algebraMap K k (M : K) = 0 := by rw [map_natCast, h]
    exact (algebraMap K k).injective (by rw [this, map_zero])
  obtain ⟨Θ, hΘ⟩ :=
    WeierstrassCurve.exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
      K M data k Ω hMk E hE hfull

  have hcyc : ∀ R : (E.baseChange Ω).toAffine.Point, addOrderOf R = M →
      IsAddCyclic (AddSubgroup.zmultiples R) ∧ Nat.card (AddSubgroup.zmultiples R) = M := by
    intro R hR
    exact ⟨inferInstance, by rw [Nat.card_zmultiples, hR]⟩
  set HP : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = M} :=
    ⟨AddSubgroup.zmultiples P, hcyc P hP⟩ with hHP
  set HQ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = M} :=
    ⟨AddSubgroup.zmultiples Q, hcyc Q hQ⟩ with hHQ

  set Φk : Polynomial k := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) E.j) with hΦk
  have hΦΩ : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) (algebraMap k Ω E.j)) =
      Φk.map (algebraMap k Ω) := by
    rw [hΦk, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp
  have hmon : Φk.Monic := data.monic.map _
  have hirr : Irreducible Φk := irreducible_fibre K data hMK hE hgen
  have hmin : ∀ y : Ω, (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω)
      (algebraMap k Ω E.j))).IsRoot y → minpoly k y = Φk := by
    intro y hy
    rw [hΦΩ, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hy
    exact (minpoly.eq_of_irreducible_of_monic hirr hy hmon).symm
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  have hconj : minpoly k ((Θ HQ).1 : Ω) = minpoly k ((Θ HP).1 : Ω) :=
    (hmin _ (Θ HQ).2).trans (hmin _ (Θ HP).2).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := k) (E := Ω)).mp hconj
  have hσ' : σ ((Θ HP).1 : Ω) = (Θ HQ).1 := hσ

  have hmapcyc : IsAddCyclic ((AddSubgroup.zmultiples P).map
      (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω))) ∧
      Nat.card ((AddSubgroup.zmultiples P).map
        (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω))) = M := by
    rw [AddMonoidHom.map_zmultiples]
    refine hcyc _ ?_
    rw [addOrderOf_injective _ (Point.map_injective (f := (σ : Ω →ₐ[k] Ω))), hP]
  set HP' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = M} :=
    ⟨(AddSubgroup.zmultiples P).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)), hmapcyc⟩
    with hHP'
  have hnat := hΘ σ HP HP' rfl
  have hEq : Θ HP' = Θ HQ := by
    apply Subtype.ext
    rw [hnat, hσ']
  have hHH : HP' = HQ := Θ.injective hEq
  have hsub : (AddSubgroup.zmultiples P).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) =
      AddSubgroup.zmultiples Q := congrArg Subtype.val hHH
  have hmem : WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P ∈ AddSubgroup.zmultiples Q := by
    rw [← hsub, AddMonoidHom.map_zmultiples]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  exact ⟨σ, n, hn.symm⟩

end Lines

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

theorem main
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)
    (P P' : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = M) (hP' : addOrderOf P' = M) :
    ∃ σ : Ω ≃ₐ[k] Ω, P' = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P := by

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
  have hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2 := by
    rw [← hcardT]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun Q => (mem_Tor_iff Q).symm)

  obtain ⟨P₁, P₂, σ₀, ε, hP₁, hP₂, hind, hε, hσ₁, hσ₂⟩ :=
    WeierstrassCurve.exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
      K M hM k Ω E hE hgen
  set T₁ : Tor Ω E M := ⟨P₁, (mem_Tor_iff P₁).mpr hP₁⟩ with hT₁
  set T₂ : Tor Ω E M := ⟨P₂, (mem_Tor_iff P₂).mpr hP₂⟩ with hT₂
  have hinj : Function.Injective (basisHom T₁ T₂) := basisHom_injective T₁ T₂ hind
  haveI : Finite (Tor Ω E M) := Nat.finite_of_card_ne_zero (by
    rw [hcardT]; exact pow_ne_zero 2 (NeZero.ne M))
  have hbij : Function.Bijective (basisHom T₁ T₂) := by
    apply hinj.bijective_of_nat_card_le
    rw [hcardT, Nat.card_prod, Nat.card_zmod, sq]
  set e : ZMod M × ZMod M ≃+ Tor Ω E M := AddEquiv.ofBijective (basisHom T₁ T₂) hbij with he_def
  have he_apply : ∀ v, e v = basisHom T₁ T₂ v := fun v => rfl
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
    obtain ⟨σ, n, hn⟩ := exists_map_mem_zmultiples K M hM k Ω E hE hgen hfull _ _ hv' hw'
    refine ⟨rho E M e σ, ⟨σ, rfl⟩, n, ?_⟩
    rw [rho_apply]
    have : actT E M σ (e v) = n • e w := by
      apply Subtype.ext
      rw [actT_apply_coe, hn, Submodule.coe_smul_of_tower]
    rw [this, map_zsmul, AddEquiv.symm_apply_apply]

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

  set TP : Tor Ω E M := ⟨P, (mem_Tor_iff P).mpr (by rw [← hP]; exact addOrderOf_nsmul_eq_zero P)⟩
    with hTP
  set TP' : Tor Ω E M := ⟨P', (mem_Tor_iff P').mpr (by rw [← hP']; exact addOrderOf_nsmul_eq_zero P')⟩
    with hTP'
  have hv : addOrderOf (e.symm TP) = M := by
    rw [AddEquiv.addOrderOf_eq, ← addOrderOf_coe_Tor]
    exact hP
  have hw : addOrderOf (e.symm TP') = M := by
    rw [AddEquiv.addOrderOf_eq, ← addOrderOf_coe_Tor]
    exact hP'
  obtain ⟨h, ⟨τ, rfl⟩, hτ⟩ :=
    AddAut.exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem M H htrans ht _ _ hv hw
  rw [rho_apply, AddEquiv.apply_symm_apply] at hτ
  have hτ' : actT E M τ TP = TP' := by
    have := congrArg e hτ
    rwa [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at this
  refine ⟨τ, ?_⟩
  have := congrArg Subtype.val hτ'
  exact this.symm

end P2MKcIgusaMonodromy
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j.P2MKcIgusaMonodromy"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j.P2MKcIgusaMonodromy"

open WeierstrassCurve WeierstrassCurve.Affine

universe u v in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)
    (P P' : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = M) (hP' : addOrderOf P' = M) :
    ∃ σ : Ω ≃ₐ[k] Ω, P' = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P :=
  P2MKcIgusaMonodromy.main K M hM k Ω E hE hgen P P' hP hP'

end S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j
end P2MW
export P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j (solution)
