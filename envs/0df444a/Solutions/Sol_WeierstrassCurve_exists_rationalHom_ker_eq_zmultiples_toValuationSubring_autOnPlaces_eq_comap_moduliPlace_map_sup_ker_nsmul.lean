-- Prove2me | solution 1 for WeierstrassCurve.exists_rationalHom_ker_eq_zmultiples_toValuationSubring_autOnPlaces_eq_comap_moduliPlace_map_sup_ker_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fdbf419b-7962-5941-8151-0a8574502f2b

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_ModularCurve_congrEquiv_moduliPlace_eq_moduliPlace_fullKernelQuotient_of_atkinLehner
import Theorems.Thm_ModularCurve_exists_moduliTestDatum_natCard_torsion_eq_sq
import Theorems.Thm_ModularCurve_eq_of_isModuliPlaceOf
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
import Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
import Theorems.Thm_WeierstrassCurve_coordsOrZero_veluPointMap2
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_rationalHom_ker_eq_zmultiples_toValuationSubring_autOnPlaces_eq_comap_moduliPlace_map_sup_ker_nsmul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.pointAddEquivOfEq_refl"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace P2MKcAtkinLehnerT

section Cleared

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem velu_pair_x_cleared {x y x₀ y₀ : R}
    (hP : W.toAffine.Equation x y) (hR : W.toAffine.Equation x₀ y₀) :
    ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
      + ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
          - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
      = W.veluT x₀ y₀ * (x - x₀) + W.veluU x₀ y₀ := by
  rw [Affine.equation_iff] at hP hR
  simp only [veluT, veluU, veluGx, veluGy]
  linear_combination 2 * hP - 2 * hR

theorem velu_pair_y_cleared {x y x₀ y₀ : R}
    (hP : W.toAffine.Equation x y) (hR : W.toAffine.Equation x₀ y₀) :
    ((-((y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) - y₀ * (x - x₀) ^ 3)
      + ((-((y + y₀ + W.a₁ * x₀ + W.a₃) * (((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2
              + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
            - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) + (y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) ^ 3)
      = -(W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃)
          + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)
          + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀)) := by
  rw [Affine.equation_iff] at hP hR
  simp only [veluT, veluU, veluGx, veluGy]
  linear_combination (-(2 * y) - 2 * W.a₁ * x + W.a₁ * x₀ - W.a₃) * hP
    + (2 * y + 2 * W.a₁ * x - W.a₁ * x₀ + W.a₃) * hR

end Cleared

section PairField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem addX_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addX x x₀ ((y - y₀) / (x - x₀)) - x₀
      = ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
          / (x - x₀) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  simp only [Affine.addX]
  field_simp
  ring1

theorem addX_neg_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addX x x₀ ((y - W.toAffine.negY x₀ y₀) / (x - x₀)) - x₀
      = ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
          - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2) / (x - x₀) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  simp only [Affine.addX, Affine.negY]
  field_simp
  ring1

theorem addY_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addY x x₀ y ((y - y₀) / (x - x₀)) - y₀
      = ((-((y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) - y₀ * (x - x₀) ^ 3) / (x - x₀) ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 hd)]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  ring1

theorem addY_neg_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addY x x₀ y ((y - W.toAffine.negY x₀ y₀) / (x - x₀)) - W.toAffine.negY x₀ y₀
      = ((-((y + y₀ + W.a₁ * x₀ + W.a₃) * (((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2
              + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
            - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) + (y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) ^ 3) / (x - x₀) ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 hd)]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  ring1

variable [DecidableEq F]

theorem velu_pair {x y x₀ y₀ : F}
    (h : W.toAffine.Nonsingular x y) (h₀ : W.toAffine.Nonsingular x₀ y₀) (hx : x ≠ x₀) :
    (((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.1
          - (Point.some x₀ y₀ h₀ : W.toAffine.Point).coordsOrZero.1)
        + ((Point.some x y h + -Point.some x₀ y₀ h₀).coordsOrZero.1
          - (-(Point.some x₀ y₀ h₀ : W.toAffine.Point)).coordsOrZero.1)
        = W.veluT x₀ y₀ / (x - x₀) + W.veluU x₀ y₀ / (x - x₀) ^ 2) ∧
    (((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.2
          - (Point.some x₀ y₀ h₀ : W.toAffine.Point).coordsOrZero.2)
        + ((Point.some x y h + -Point.some x₀ y₀ h₀).coordsOrZero.2
          - (-(Point.some x₀ y₀ h₀ : W.toAffine.Point)).coordsOrZero.2)
        = -(W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃) / (x - x₀) ^ 3
            + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2
            + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) / (x - x₀) ^ 2)) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hP : W.toAffine.Equation x y := h.1
  have hR : W.toAffine.Equation x₀ y₀ := h₀.1
  rw [Point.neg_some h₀, Point.add_of_X_ne hx, Point.add_of_X_ne hx]
  simp only [Point.coordsOrZero_some, slope_of_X_ne hx]
  refine ⟨?_, ?_⟩
  · rw [addX_sub_eq_div W hd, addX_neg_sub_eq_div W hd, ← add_div, velu_pair_x_cleared W hP hR,
      div_add_div _ _ hd (pow_ne_zero 2 hd),
      div_eq_div_iff (pow_ne_zero 2 hd) (mul_ne_zero hd (pow_ne_zero 2 hd))]
    ring
  · rw [addY_sub_eq_div W hd, addY_neg_sub_eq_div W hd, ← add_div, velu_pair_y_cleared W hP hR,
      neg_div, neg_inj, div_add_div _ _ (pow_ne_zero 3 hd) (pow_ne_zero 2 hd), div_add_div _ _
        (mul_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hd)) (pow_ne_zero 2 hd),
      div_eq_div_iff (pow_ne_zero 3 hd)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hd)) (pow_ne_zero 2 hd))]
    ring

end PairField

theorem sum_Icc_two_mul_eq_sum_pairs {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * n), f k = ∑ k ∈ Finset.Icc 1 n, (f k + f (2 * n + 1 - k)) := by
  rw [Finset.sum_add_distrib]
  have hsplit : Finset.Icc 1 (2 * n) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (2 * n) := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (2 * n)) := by
    rw [Finset.disjoint_left]; intro k hk hk'; simp only [Finset.mem_Icc] at hk hk'; omega
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  refine Finset.sum_nbij' (fun k => 2 * n + 1 - k) (fun k => 2 * n + 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; congr 1; omega

theorem nsmul_ne_zero_of_pos_of_le {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    (Q : W.toAffine.Point) {N : ℕ} (hQ : addOrderOf Q = N) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N - 1) :
    k • Q ≠ 0 := by
  intro h
  have hdvd : N ∣ k := hQ ▸ addOrderOf_dvd_of_nsmul_eq_zero h
  have hle : N ≤ k := Nat.le_of_dvd hk1 hdvd
  omega

theorem fullKernelPin_eq_veluXY_of_odd
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    {x y : F} (h : W.toAffine.Nonsingular x y)
    (hP : (Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    (x + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
        (((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
     y + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
        (((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) =
      (W.veluX (W.oddOrderSummingSet Q n) x, W.veluY (W.oddOrderSummingSet Q n) x y) := by
  classical
  have h2n : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel (2 * n) 1
  have hord : (2 * n + 1) • Q = 0 := hQ ▸ addOrderOf_nsmul_eq_zero Q
  have hrefl : ∀ k, k ≤ 2 * n + 1 → (2 * n + 1 - k) • Q = -(k • Q) := by
    intro k hk
    rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hk, hord]

  have haff : ∀ k, 1 ≤ k → k ≤ 2 * n →
      ∃ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀), k • Q = Point.some x₀ y₀ h₀ ∧ x ≠ x₀ := by
    intro k hk1 hk2
    have hne : k • Q ≠ 0 := nsmul_ne_zero_of_pos_of_le Q hQ hk1 (by omega)
    rcases hkQ : k • Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hkQ hne
    · refine ⟨x₀, y₀, h₀, rfl, ?_⟩
      intro hxx
      apply hP
      rcases Affine.Y_eq_of_X_eq h.1 h₀.1 hxx with hyy | hyy
      · have hPt : (Point.some x y h : W.toAffine.Point) = k • Q := by
          rw [hkQ]; subst hxx; subst hyy; rfl
        rw [hPt]
        exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k
      · have hPt : (Point.some x y h : W.toAffine.Point) = -(k • Q) := by
          rw [hkQ, Point.neg_some]; subst hxx; subst hyy; rfl
        rw [hPt]
        exact AddSubgroup.neg_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)

  have hpair : ∀ k ∈ Finset.Icc 1 n,
      ((((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1)
        + (((Point.some x y h : W.toAffine.Point) + (2 * n + 1 - k) • Q).coordsOrZero.1
            - ((2 * n + 1 - k) • Q).coordsOrZero.1)
        = W.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 / (x - (k • Q).coordsOrZero.1)
          + W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 / (x - (k • Q).coordsOrZero.1) ^ 2) ∧
      ((((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)
        + (((Point.some x y h : W.toAffine.Point) + (2 * n + 1 - k) • Q).coordsOrZero.2
            - ((2 * n + 1 - k) • Q).coordsOrZero.2)
        = -(W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 * (2 * y + W.a₁ * x + W.a₃)
              / (x - (k • Q).coordsOrZero.1) ^ 3
            + W.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
              * (W.a₁ * (x - (k • Q).coordsOrZero.1) + y - (k • Q).coordsOrZero.2)
              / (x - (k • Q).coordsOrZero.1) ^ 2
            + (W.a₁ * W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
                - W.veluGx (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
                  * W.veluGy (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2)
              / (x - (k • Q).coordsOrZero.1) ^ 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨x₀, y₀, h₀, hkQ, hx⟩ := haff k hk.1 (by omega)
    rw [hrefl k (by omega), hkQ]
    exact velu_pair W h h₀ hx

  have hinj : ∀ k ∈ Finset.Icc 1 n, ∀ k' ∈ Finset.Icc 1 n,
      (k • Q).coordsOrZero = (k' • Q).coordsOrZero → k = k' := by
    intro k hk k' hk' hkk
    rw [Finset.mem_Icc] at hk hk'
    obtain ⟨x₀, y₀, h₀, hkQ, -⟩ := haff k hk.1 (by omega)
    obtain ⟨x₁, y₁, h₁, hk'Q, -⟩ := haff k' hk'.1 (by omega)
    have hpt : k • Q = k' • Q := by
      rw [hkQ, hk'Q] at hkk ⊢
      simp only [Point.coordsOrZero_some, Prod.mk.injEq] at hkk
      obtain ⟨rfl, rfl⟩ := hkk
      rfl
    have hmod := (nsmul_inj_mod (x := Q)).mp hpt
    rwa [hQ, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod

  rw [h2n]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [sum_Icc_two_mul_eq_sum_pairs, Finset.sum_congr rfl (fun k hk => (hpair k hk).1)]
    simp only [veluX, oddOrderSummingSet, Finset.sum_image hinj]
  · dsimp only
    rw [sum_Icc_two_mul_eq_sum_pairs, Finset.sum_congr rfl (fun k hk => (hpair k hk).2)]
    simp only [veluY, oddOrderSummingSet, Finset.sum_image hinj, Finset.sum_neg_distrib,
      sub_eq_add_neg]

theorem coordsOrZero_eq_translationSum
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    (φ : W.toAffine.Point →+ (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Point)
    (hφ : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (W.veluX (W.oddOrderSummingSet Q n) x)
          (W.veluY (W.oddOrderSummingSet Q n) x y) h')
    (P : W.toAffine.Point) (hP : P ∉ AddSubgroup.zmultiples Q) :
    (φ P).coordsOrZero =
      (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
          ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
       P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
          ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd (AddSubgroup.zero_mem _) hP
  · obtain ⟨h', hφP⟩ := hφ x y h hP
    rw [hφP, Point.coordsOrZero_some, Point.coordsOrZero_some]
    exact (fullKernelPin_eq_veluXY_of_odd W Q n hQ h hP).symm

section Pick

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

theorem exists_velu_pick (q : ℕ) [NeZero q] (hq : q.Prime) (hq0 : ((q : ℕ) : κ) ≠ 0)
    (E : WeierstrassCurve κ) [E.IsElliptic] (Q : E.toAffine.Point) (hQ : addOrderOf Q = q) :
    ∃ (A : WeierstrassCurve κ) (_ : E.fullKernelQuotient Q q = A) (_ : A.IsElliptic)
      (φ : E.toAffine.Point →+ A.toAffine.Point),
      φ ∈ rationalHomSet κ E A ∧ φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : E.toAffine.Point →+ V.toAffine.Point),
        α ∈ rationalHomSet κ E V → α Q = 0 → ∃ γ ∈ rationalHomSet κ A V, α = γ.comp φ) ∧
      ∀ P : E.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
        (φ P).coordsOrZero =
          (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (q - 1),
              ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
           P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (q - 1),
              ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hQ
    exact hq.one_lt.ne' (hQ ▸ rfl)
  have hqQ : q • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hΔf : (E.fullKernelQuotient Q q).Δ ≠ 0 := fullKernelQuotient_discriminant_ne_zero q E hq0 Q hQ
  rcases hq.eq_two_or_odd' with h2 | hodd
  ·
    subst h2
    have h20 : (2 : κ) ≠ 0 := by exact_mod_cast hq0
    rcases Q with _ | ⟨x₀, y₀, hns⟩
    · exact absurd rfl hQ0
    have hneg : -(Affine.Point.some x₀ y₀ hns) = Affine.Point.some x₀ y₀ hns := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul, hqQ]
    have hy₀ : E.toAffine.negY x₀ y₀ = y₀ := by
      rw [Affine.Point.neg_some] at hneg
      exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp hneg).2
    have hgy : E.veluGy x₀ y₀ = 0 := E.veluGy_eq_zero_of_negY_eq hy₀
    have hA2 : E.fullKernelQuotient (.some x₀ y₀ hns) 2 = E.veluQuotient2 x₀ y₀ :=
      fullKernelQuotient_two E hns hgy
    have hΔ2 : (E.veluQuotient2 x₀ y₀).Δ ≠ 0 := hA2 ▸ hΔf
    haveI hA : (E.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ2⟩
    obtain ⟨π₀, hπcoe, hπrat, -, hπuniv⟩ :=
      exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul h20 E hns.1 hgy hΔ2
    have hπapp : ∀ P : E.toAffine.Point, π₀ P = veluPointMap2 h20 hns.1 hgy hΔ2 P := fun P => by
      rw [hπcoe]
    have hπQ : π₀ (.some x₀ y₀ hns) = 0 := by
      rw [hπapp]; exact veluPointMap2_some_of_eq h20 hns.1 hgy hΔ2 hns rfl
    have hπker : π₀.ker = AddSubgroup.zmultiples (Affine.Point.some x₀ y₀ hns) := by
      refine le_antisymm ?_ ((AddSubgroup.zmultiples_le_of_mem) hπQ)
      intro P hP
      rw [AddMonoidHom.mem_ker] at hP
      rcases P with _ | ⟨x, y, h⟩
      · exact zero_mem _
      · by_cases hx : x = x₀
        · subst hx
          have hy : y = y₀ := by
            rcases eq_or_ne y (E.toAffine.negY x y₀) with h1 | h1
            · rw [h1, hy₀]
            · exact Affine.Y_eq_of_Y_ne h.1 hns.1 rfl h1
          subst hy
          exact AddSubgroup.mem_zmultiples _
        · exfalso
          rw [hπapp] at hP
          exact Affine.Point.some_ne_zero _ ((veluPointMap2_some_of_ne h20 hns.1 hgy hΔ2 h hx).symm.trans hP)
    refine ⟨E.veluQuotient2 x₀ y₀, hA2, hA, π₀, hπrat, hπker, fun V _ α hα hαQ => ?_, fun P hP => ?_⟩
    · refine hπuniv V inferInstance α hα fun T hT => ?_
      have hT' : T ∈ π₀.ker := hT
      rw [hπker] at hT'
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT'
      rw [map_zsmul]
      exact (congrArg (k • ·) hαQ).trans (smul_zero k)
    · rw [hπapp]
      exact WeierstrassCurve.coordsOrZero_veluPointMap2 E h20 hns hgy hΔ2 P hP
  ·
    have hq2 : q ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have hqn : q = 2 * (q / 2) + 1 := (Nat.two_mul_div_two_add_one_of_odd hodd).symm
    have hQ' : addOrderOf Q = 2 * (q / 2) + 1 := hQ.trans hqn
    have hAv : E.fullKernelQuotient Q q = E.veluQuotient (E.oddOrderSummingSet Q (q / 2)) := by
      have h := fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet E Q (q / 2) hQ'
      rwa [← hqn] at h
    have hΔv : (E.veluQuotient (E.oddOrderSummingSet Q (q / 2))).Δ ≠ 0 := hAv ▸ hΔf
    haveI hA : (E.veluQuotient (E.oddOrderSummingSet Q (q / 2))).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr hΔv⟩
    obtain ⟨φ₀, hker, hφ₀⟩ := exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed E hq hq2 hq0 Q hQ
    obtain ⟨hφrat, huniv⟩ :=
      veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq E (q / 2) Q hQ' φ₀ hker hφ₀
    refine ⟨E.veluQuotient (E.oddOrderSummingSet Q (q / 2)), hAv, hA, φ₀, hφrat, hker,
      fun V _ α hα hαQ => huniv V α hα hαQ, fun P hP => ?_⟩
    have h := coordsOrZero_eq_translationSum E Q (q / 2) hQ' φ₀ hφ₀ P hP
    rwa [← hqn] at h

end Pick

section Level

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

private theorem _root_.P2MKcAtkinLehnerT.exists_generator {G : Type*} [AddGroup G] (C : AddSubgroup G) (hC : IsAddCyclic C) {n : ℕ}
    (hn : Nat.card C = n) : ∃ g : G, addOrderOf g = n ∧ AddSubgroup.zmultiples g = C := by
  haveI := hC
  obtain ⟨⟨g, hg⟩, hgen⟩ := IsAddCyclic.exists_generator (α := C)
  have hC' : AddSubgroup.zmultiples g = C := by
    refine le_antisymm (AddSubgroup.zmultiples_le.mpr hg) fun x hx => ?_
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen ⟨x, hx⟩)
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨z, ?_⟩
    have := congrArg Subtype.val hz
    simpa using this
  refine ⟨g, ?_, hC'⟩
  rw [← Nat.card_zmultiples, hC', hn]

p2m_export "P2MKcAtkinLehnerT" "exists_generator"

theorem zmultiples_eq_zmultiples_nsmul {G : Type*} [AddCommGroup G] {g Q : G} {N q : ℕ}
    (hN : N ≠ 0) (hq : q ≠ 0) (hg : addOrderOf g = N * q) (hQ : Q ∈ AddSubgroup.zmultiples g)
    (hQq : addOrderOf Q = q) : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (N • g) := by
  have hordNg : addOrderOf (N • g) = q := by
    rw [addOrderOf_nsmul' g hN, hg, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hN)]
  haveI : Finite (AddSubgroup.zmultiples (N • g)) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hordNg]; exact hq)
  apply AddSubgroup.eq_of_le_of_card_ge
  · obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hQ
    have h1 : ((q : ℤ) * z) • g = 0 := by
      rw [mul_zsmul, natCast_zsmul, ← hQq, addOrderOf_nsmul_eq_zero]
    have h2 : (addOrderOf g : ℤ) ∣ (q : ℤ) * z := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
    rw [hg] at h2
    obtain ⟨w, hw⟩ := h2
    have hz : z = N * w := by
      have h3 : (q : ℤ) * z = q * (N * w) := by rw [hw]; push_cast; ring
      exact mul_left_cancel₀ (by exact_mod_cast hq) h3
    refine AddSubgroup.zmultiples_le.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨w, ?_⟩)
    rw [hz, mul_comm, mul_zsmul, natCast_zsmul]
  · rw [Nat.card_zmultiples, Nat.card_zmultiples, hordNg, hQq]

theorem mem_zmultiples_add_of_coprime {G : Type*} [AddCommGroup G] {N q : ℕ} (hcop : Nat.Coprime N q)
    {u w : G} (hu : N • u = 0) (hw : q • w = 0) :
    u ∈ AddSubgroup.zmultiples (u + w) ∧ w ∈ AddSubgroup.zmultiples (u + w) := by
  obtain ⟨α, β, hαβ⟩ : IsCoprime (N : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hu' : (N : ℤ) • u = 0 := by rw [natCast_zsmul]; exact hu
  have hw' : (q : ℤ) • w = 0 := by rw [natCast_zsmul]; exact hw
  have hu1 : (β * (q : ℤ)) • u = u := by
    have h1 : (α * (N : ℤ) + β * (q : ℤ)) • u = u := by rw [hαβ, one_smul]
    rwa [add_smul, mul_smul α, hu', smul_zero, zero_add] at h1
  have hw1 : (α * (N : ℤ)) • w = w := by
    have h1 : (α * (N : ℤ) + β * (q : ℤ)) • w = w := by rw [hαβ, one_smul]
    rwa [add_smul, mul_smul β, hw', smul_zero, add_zero] at h1
  constructor
  · refine AddSubgroup.mem_zmultiples_iff.mpr ⟨β * q, ?_⟩
    rw [smul_add, hu1, mul_smul, hw', smul_zero, add_zero]
  · refine AddSubgroup.mem_zmultiples_iff.mpr ⟨α * N, ?_⟩
    rw [smul_add, hw1, mul_smul, hu', smul_zero, zero_add]

theorem exists_torsion_not_mem (E : WeierstrassCurve κ) [E.IsElliptic] {q : ℕ} (hq : q.Prime)
    (hqκ : (q : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = q) :
    ∃ t : E.toAffine.Point, q • t = 0 ∧ t ∉ AddSubgroup.zmultiples Q := by
  by_contra hcon
  have hcon' : ∀ t : E.toAffine.Point, q • t = 0 → t ∈ AddSubgroup.zmultiples Q := by
    intro t ht
    by_contra h
    exact hcon ⟨t, ht, h⟩
  have hcard : Nat.card (Submodule.torsionBy ℤ E.toAffine.Point (q : ℤ)) = q ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) E hqκ
  haveI : Finite (AddSubgroup.zmultiples Q) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hQ]; exact hq.ne_zero)
  have hmemQ : ∀ P : Submodule.torsionBy ℤ E.toAffine.Point (q : ℤ),
      (P : E.toAffine.Point) ∈ AddSubgroup.zmultiples Q := by
    intro P
    refine hcon' P.1 ?_
    have := (Submodule.mem_torsionBy_iff (q : ℤ) P.1).mp P.2
    rwa [natCast_zsmul] at this
  have hle : Nat.card (Submodule.torsionBy ℤ E.toAffine.Point (q : ℤ)) ≤
      Nat.card (AddSubgroup.zmultiples Q) := by
    refine Nat.card_le_card_of_injective (fun P => (⟨P.1, hmemQ P⟩ : AddSubgroup.zmultiples Q)) ?_
    intro P P' h
    exact Subtype.ext (congrArg (fun s : AddSubgroup.zmultiples Q => (s : E.toAffine.Point)) h)
  rw [hcard, Nat.card_zmultiples, hQ, pow_two] at hle
  have h3 : q * q ≤ q * 1 := by simpa using hle
  have h4 : q ≤ 1 := Nat.le_of_mul_le_mul_left h3 (by have := hq.two_le; omega)
  exact absurd h4 (by have := hq.two_le; omega)

theorem torsion_mem_sup (E : WeierstrassCurve κ) [E.IsElliptic] {q : ℕ} (hq : q.Prime)
    (hqκ : (q : κ) ≠ 0) (Q : E.toAffine.Point) (hQ : addOrderOf Q = q) (t : E.toAffine.Point)
    (ht : q • t = 0) (htQ : t ∉ AddSubgroup.zmultiples Q) (T : E.toAffine.Point) (hT : q • T = 0) :
    ∃ i j : ℤ, T = i • Q + j • t := by
  haveI : Fact q.Prime := ⟨hq⟩
  set Tq : AddSubgroup E.toAffine.Point :=
    (Submodule.torsionBy ℤ E.toAffine.Point (q : ℤ)).toAddSubgroup with hTq
  have hmemTq : ∀ P : E.toAffine.Point, P ∈ Tq ↔ q • P = 0 := by
    intro P
    rw [hTq, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff, ← natCast_zsmul]
  have hcardTq : Nat.card Tq = q ^ 2 := by
    rw [hTq]
    exact WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) E hqκ
  haveI hfin : Finite Tq := Nat.finite_of_card_ne_zero (by rw [hcardTq]; exact pow_ne_zero 2 hq.ne_zero)
  have hqQ : q • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  set H : AddSubgroup E.toAffine.Point := AddSubgroup.zmultiples Q ⊔ AddSubgroup.zmultiples t with hH
  have hHle : H ≤ Tq := by
    rw [hH, sup_le_iff]
    constructor
    · rw [AddSubgroup.zmultiples_le]; exact (hmemTq Q).mpr hqQ
    · rw [AddSubgroup.zmultiples_le]; exact (hmemTq t).mpr ht
  haveI : Finite H := Finite.of_injective (AddSubgroup.inclusion hHle) (AddSubgroup.inclusion_injective hHle)
  have hdvd : Nat.card H ∣ q ^ 2 := hcardTq ▸ AddSubgroup.card_dvd_of_le hHle
  obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  have hQle : AddSubgroup.zmultiples Q ≤ H := le_sup_left
  have hcardQ : Nat.card (AddSubgroup.zmultiples Q) = q := by rw [Nat.card_zmultiples, hQ]
  have hk2 : k = 2 := by
    interval_cases k
    · exfalso
      have hq1 : q ∣ 1 := by
        have := AddSubgroup.card_dvd_of_le hQle
        rwa [hcardQ, hkH, pow_zero] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp hq1)
    · exfalso
      rw [pow_one] at hkH
      have heq : AddSubgroup.zmultiples Q = H :=
        AddSubgroup.eq_of_le_of_card_ge hQle (by rw [hkH, hcardQ])
      have htH : t ∈ H := (le_sup_right : AddSubgroup.zmultiples t ≤ H) (AddSubgroup.mem_zmultiples t)
      rw [← heq] at htH
      exact htQ htH
    · rfl
  rw [hk2] at hkH
  have hHeq : H = Tq := AddSubgroup.eq_of_le_of_card_ge hHle (by rw [hkH, hcardTq])
  have hTH : T ∈ H := by rw [hHeq]; exact (hmemTq T).mpr hT
  rw [hH] at hTH
  obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp hTH
  obtain ⟨i, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
  exact ⟨i, j, hyz.symm⟩

theorem map_sup_eq_zmultiples {E E' : WeierstrassCurve κ} [E.IsElliptic] {N q : ℕ} (hq : q.Prime)
    (hN : N ≠ 0) (hcop : Nat.Coprime N q) (hqκ : (q : κ) ≠ 0)
    (g₀ : E.toAffine.Point) (hg₀ : addOrderOf g₀ = N * q)
    (φ : E.toAffine.Point →+ E'.toAffine.Point) (hφker : φ.ker = AddSubgroup.zmultiples (N • g₀))
    (t₀ : E.toAffine.Point) (ht₀ : q • t₀ = 0) (ht₀Q : t₀ ∉ AddSubgroup.zmultiples (N • g₀)) :
    (AddSubgroup.zmultiples g₀ ⊔ (((q : ℕ)) • AddMonoidHom.id E.toAffine.Point).ker).map φ =
        AddSubgroup.zmultiples (φ g₀ + φ t₀) ∧
      addOrderOf (φ g₀ + φ t₀) = N * q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hordQ : addOrderOf (N • g₀) = q := by
    rw [addOrderOf_nsmul' g₀ hN, hg₀, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hN)]
  have hφQ : φ (N • g₀) = 0 := (AddMonoidHom.mem_ker).mp (hφker ▸ AddSubgroup.mem_zmultiples (N • g₀))
  have hNu : N • φ g₀ = 0 := by rw [← map_nsmul, hφQ]
  have hqw : q • φ t₀ = 0 := by rw [← map_nsmul, ht₀, map_zero]
  have hw0 : φ t₀ ≠ 0 := fun h => ht₀Q (hφker ▸ (AddMonoidHom.mem_ker).mpr h)
  have hordw : addOrderOf (φ t₀) = q := addOrderOf_eq_prime hqw hw0
  have hordu : addOrderOf (φ g₀) = N := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hNu) ?_
    have ho : addOrderOf (φ g₀) • g₀ ∈ φ.ker := by
      rw [AddMonoidHom.mem_ker, map_nsmul]; exact addOrderOf_nsmul_eq_zero _
    rw [hφker] at ho
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ho
    have h1 : ((addOrderOf (φ g₀) : ℤ) - k * N) • g₀ = 0 := by
      rw [sub_smul, natCast_zsmul, ← hk, mul_smul, natCast_zsmul, sub_self]
    have h2 : ((N * q : ℕ) : ℤ) ∣ (addOrderOf (φ g₀) : ℤ) - k * N := by
      rw [← hg₀]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
    have h3 : (N : ℤ) ∣ (addOrderOf (φ g₀) : ℤ) := by
      have h4 : (N : ℤ) ∣ (addOrderOf (φ g₀) : ℤ) - k * N := (Dvd.intro (q : ℤ) (by push_cast; ring)).trans h2
      have h5 : (N : ℤ) ∣ k * N := Dvd.intro_left _ rfl
      simpa using dvd_add h4 h5
    exact_mod_cast h3
  obtain ⟨hu_mem, hw_mem⟩ := mem_zmultiples_add_of_coprime hcop hNu hqw
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨c, hc, e, he, rfl⟩ := AddSubgroup.mem_sup.mp hT
    rw [map_add]
    refine add_mem ?_ ?_
    · obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hc
      rw [map_zsmul]
      exact AddSubgroup.zsmul_mem _ hu_mem k
    · have hqe : q • e = 0 := by
        have := (AddMonoidHom.mem_ker).mp he
        rwa [AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply] at this
      obtain ⟨i, j, rfl⟩ := torsion_mem_sup E hq hqκ (N • g₀) hordQ t₀ ht₀ ht₀Q e hqe
      rw [map_add, map_zsmul, map_zsmul, hφQ, smul_zero, zero_add]
      exact AddSubgroup.zsmul_mem _ hw_mem j
  · rw [AddSubgroup.zmultiples_le, ← map_add]
    refine ⟨g₀ + t₀, ?_, rfl⟩
    refine AddSubgroup.mem_sup.mpr ⟨g₀, AddSubgroup.mem_zmultiples g₀, t₀, ?_, rfl⟩
    rw [AddMonoidHom.mem_ker, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, ht₀]
  · rw [(AddCommute.all _ _).addOrderOf_add_eq_mul_addOrderOf_of_coprime (by rw [hordu, hordw]; exact hcop),
      hordu, hordw]

end Level

section Descent

variable (κ : Type) [Field κ] (N q : ℕ) [NeZero N] [NeZero q]

theorem inclusion_symm_eq_symm_inclusion
    (hM : jqNModC κ N ∈ modularFunctionFieldC κ (N * q)) (hs : jqNModC κ q ∈ modularFunctionFieldC κ (N * q))
    (σ : ↥(modularFunctionFieldC κ (N * q)) ≃ₐ[κ] ↥(modularFunctionFieldC κ (N * q)))
    (hσ : IsAtkinLehnerLevelAut κ N q hM hs σ)
    (τ : modularFunctionFieldFullC κ (N * q) ≃ₐ[κ] modularFunctionFieldFullC κ (N * q))
    (hτ : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N),
      τ ⟨qExpand κ d (jqModC κ), jqModCd_mem_full κ (N * q) (Dvd.dvd.mul_right hd q)⟩
          = ⟨qExpand κ (d * q) (jqModC κ), jqModCd_mem_full κ (N * q) (Nat.mul_dvd_mul_right hd q)⟩
        ∧ τ ⟨qExpand κ (d * q) (jqModC κ), jqModCd_mem_full κ (N * q) (Nat.mul_dvd_mul_right hd q)⟩
          = ⟨qExpand κ d (jqModC κ), jqModCd_mem_full κ (N * q) (Dvd.dvd.mul_right hd q)⟩)
    (f : ↥(modularFunctionFieldC κ (N * q))) :
    IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q)) (σ.symm f) =
      τ.symm (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q)) f) := by
  have hle := modularFunctionFieldC_le_full κ (N * q)
  suffices h : (IntermediateField.inclusion hle).comp σ.symm.toAlgHom =
      τ.symm.toAlgHom.comp (IntermediateField.inclusion hle) by
    have := DFunLike.congr_fun h f
    simpa using this
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := κ) (S := modularFunctionFieldC κ (N * q))
    (s := {jqModC κ, jqNModC κ (N * q)}) rfl ?_
  intro x hx
  show IntermediateField.inclusion hle (σ.symm _) = τ.symm (IntermediateField.inclusion hle _)
  rcases hx with rfl | hx
  ·
    have h1 : σ.symm ⟨jqModC κ, jqModC_mem κ (N * q)⟩ = ⟨jqNModC κ q, hs⟩ := by
      rw [AlgEquiv.symm_apply_eq]
      exact hσ.2.1.symm
    rw [h1, eq_comm, AlgEquiv.symm_apply_eq]
    have h3 : IntermediateField.inclusion hle ⟨jqNModC κ q, hs⟩ =
        ⟨qExpand κ (1 * q) (jqModC κ), jqModCd_mem_full κ (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ := by
      apply Subtype.ext
      rw [IntermediateField.coe_inclusion]
      show qExpand κ q (jqModC κ) = qExpand κ (1 * q) (jqModC κ)
      rw [qExpand_congr (one_mul q)]
    have h4 : IntermediateField.inclusion hle ⟨jqModC κ, jqModC_mem κ (N * q)⟩ =
        ⟨qExpand κ 1 (jqModC κ), jqModCd_mem_full κ (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ := by
      apply Subtype.ext
      show jqModC κ = qExpand κ 1 (jqModC κ)
      rw [qExpand_one_apply]
    rw [h3, (hτ 1 inferInstance (one_dvd N)).2, h4]
  ·
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h1 : σ.symm ⟨jqNModC κ (N * q), jqNModC_mem κ (N * q)⟩ = ⟨jqNModC κ N, hM⟩ := by
      rw [AlgEquiv.symm_apply_eq]
      exact hσ.2.2.2.symm
    rw [h1, eq_comm, AlgEquiv.symm_apply_eq]
    have h3 : IntermediateField.inclusion hle ⟨jqNModC κ N, hM⟩ =
        ⟨qExpand κ N (jqModC κ), jqModCd_mem_full κ (N * q) (Dvd.dvd.mul_right dvd_rfl q)⟩ :=
      Subtype.ext (IntermediateField.coe_inclusion _ _)
    have h4 : IntermediateField.inclusion hle ⟨jqNModC κ (N * q), jqNModC_mem κ (N * q)⟩ =
        ⟨qExpand κ (N * q) (jqModC κ), jqModCd_mem_full κ (N * q) (Nat.mul_dvd_mul_right dvd_rfl q)⟩ :=
      Subtype.ext (IntermediateField.coe_inclusion _ _)
    rw [h3, (hτ N inferInstance dvd_rfl).1, h4]

end Descent

end P2MKcAtkinLehnerT

end

open P2MKcAtkinLehnerT in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [CharP κ q'] (N q : ℕ) [NeZero N] [NeZero q] (hqp : q.Prime) (hqN : ¬ q ∣ N) (hq'Nq : ¬ q' ∣ N * q)
    (hM : jqNModC κ N ∈ modularFunctionFieldC κ (N * q)) (hs : jqNModC κ q ∈ modularFunctionFieldC κ (N * q))
    (σ : ↥(modularFunctionFieldC κ (N * q)) ≃ₐ[κ] ↥(modularFunctionFieldC κ (N * q)))
    (hσ : IsAtkinLehnerLevelAut κ N q hM hs σ)
    (E : WeierstrassCurve κ) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) (hC : IsAddCyclic C) (hCcard : Nat.card C = N * q)
    (Q : E.toAffine.Point) (hQC : Q ∈ C) (hQ : addOrderOf Q = q) :
    ∃ (E' : WeierstrassCurve κ) (_ : E'.IsElliptic) (φ : E.toAffine.Point →+ E'.toAffine.Point),
      φ ∈ WeierstrassCurve.rationalHomSet κ E E' ∧ φ.ker = AddSubgroup.zmultiples Q ∧ Function.Surjective φ ∧
      (∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : E.toAffine.Point →+ V.toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ E V → α Q = 0 →
          ∃ γ : E'.toAffine.Point →+ V.toAffine.Point,
            γ ∈ WeierstrassCurve.rationalHomSet κ E' V ∧ α = γ.comp φ) ∧
      ∀ P : Place κ ↥(modularFunctionFieldC κ (N * q)),
        P.toValuationSubring =
          (moduliPlace κ (N * q) E C).toValuationSubring.comap
            (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).toRingHom →
        (autOnPlaces κ N q σ P).toValuationSubring =
          (moduliPlace κ (N * q) E' ((C ⊔ (((q : ℕ)) • AddMonoidHom.id E.toAffine.Point).ker).map φ)).toValuationSubring.comap
            (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).toRingHom := by
  classical
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne q)⟩
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNq : ((N * q : ℕ) : κ) ≠ 0 := fun h => hq'Nq ((CharP.cast_eq_zero_iff κ q' (N * q)).mp h)
  have hNκ : ((N : ℕ) : κ) ≠ 0 := fun h =>
    hq'Nq (dvd_mul_of_dvd_left ((CharP.cast_eq_zero_iff κ q' N).mp h) q)
  have hqκ : ((q : ℕ) : κ) ≠ 0 := fun h =>
    hq'Nq (dvd_mul_of_dvd_right ((CharP.cast_eq_zero_iff κ q' q).mp h) N)
  have hcop : Nat.Coprime N q := ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqN).symm

  obtain ⟨A, hA, hAe, φ, hφrat, hφker, huniv, hφc⟩ := exists_velu_pick q hqp hqκ E Q hQ
  subst hA
  have hΔ : (E.fullKernelQuotient Q q).Δ ≠ 0 := fullKernelQuotient_discriminant_ne_zero q E hqκ Q hQ
  have hsurj : Function.Surjective φ :=
    WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed E hqκ Q hQ φ hφker hφc
  refine ⟨E.fullKernelQuotient Q q, hAe, φ, hφrat, hφker, hsurj,
    fun V _ α hα hαQ => ?_, fun P hP => ?_⟩
  · obtain ⟨γ, hγ, hαγ⟩ := huniv V α hα hαQ
    exact ⟨γ, hγ, hαγ⟩

  obtain ⟨g₀, hg₀, hCg⟩ := exists_generator C hC hCcard
  have hQg : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples (N • g₀) :=
    zmultiples_eq_zmultiples_nsmul hN0 (NeZero.ne q) hg₀ (hCg.symm ▸ hQC) hQ
  have hordQ' : addOrderOf (N • g₀) = q := by
    rw [addOrderOf_nsmul' g₀ hN0, hg₀, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hN0)]
  obtain ⟨t₀, ht₀, ht₀Q⟩ := exists_torsion_not_mem E hqp hqκ (N • g₀) hordQ'
  have hφker' : φ.ker = AddSubgroup.zmultiples (N • g₀) := hφker.trans hQg
  obtain ⟨hC''eq, hordsum⟩ := map_sup_eq_zmultiples hqp hN0 hcop hqκ g₀ hg₀ φ hφker' t₀ ht₀ ht₀Q
  set C'' := (C ⊔ (((q : ℕ)) • AddMonoidHom.id E.toAffine.Point).ker).map φ with hC''def
  have hC''eq' : C'' = AddSubgroup.zmultiples (φ g₀ + φ t₀) := by rw [hC''def, ← hCg, hC''eq]
  have hC'' : IsAddCyclic C'' ∧ Nat.card C'' = N * q := by
    rw [hC''eq']
    exact ⟨inferInstance, (Nat.card_zmultiples _).trans hordsum⟩
  have hCC'' : ∀ T ∈ C, φ T ∈ C'' := fun T hT =>
    ⟨T, (le_sup_left : C ≤ C ⊔ _) hT, rfl⟩
  have hqC'' : ∀ T : E.toAffine.Point, q • T = 0 → φ T ∈ C'' := fun T hT =>
    ⟨T, (le_sup_right : _ ≤ C ⊔ _) (by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply, hT]), rfl⟩

  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd κ N q hqp hqN hNκ hqκ
  have huniq : ∀ (x : ModuliPoint (N * q) κ) (v v' : Place κ (modularFunctionFieldFullC κ (N * q))),
      IsModuliPlaceOf κ (N * q) x v → IsModuliPlaceOf κ (N * q) x v' → v = v' :=
    fun x v v' h h' => ModularCurve.eq_of_isModuliPlaceOf κ (N * q) hNq x v v' h h'
  have hexT : ∀ x : ModuliPoint (N * q) κ,
      ∃ (Ω : Type) (_ : Field Ω) (_ : DecidableEq Ω) (_ : Algebra κ Ω)
        (D : ModuliTestDatum κ (N * q) x Ω),
        Nat.card {P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point // q • P = 0}
            = q ^ 2 ∧
        ∀ [DecidableEq (IsLocalRing.ResidueField D.W.toValuationSubring)]
          (P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point),
          q • P = 0 → reduceHom D.map_Δ_ne_zero P = 0 → P = 0 := by
    intro x
    obtain ⟨Ω, iF, iD, iA, D, hcard, hinj⟩ :=
      ModularCurve.exists_moduliTestDatum_natCard_torsion_eq_sq κ (N * q) hNq x
    refine ⟨Ω, iF, iD, iA, D, hcard q (dvd_mul_left q N), ?_⟩
    intro inst P₁ hqP h0
    exact hinj P₁ (by rw [← smul_smul, hqP, smul_zero]) h0
  have hlaw := ModularCurve.congrEquiv_moduliPlace_eq_moduliPlace_fullKernelQuotient_of_atkinLehner
    κ N q hqp hqN hNq huniq hexT τ hτ E C ⟨hC, hCcard⟩ Q hQC hQ hΔ φ hφker hφc C'' hC'' hCC'' hqC''

  rw [← hlaw]
  have key : ∀ g : ↥(modularFunctionFieldC κ (N * q)),
      (IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).toRingHom
          ((σ.toRingEquiv.symm : ↥(modularFunctionFieldC κ (N * q)) →+* ↥(modularFunctionFieldC κ (N * q))) g) =
        (τ.toRingEquiv.symm : ↥(modularFunctionFieldFullC κ (N * q)) →+* ↥(modularFunctionFieldFullC κ (N * q)))
          ((IntermediateField.inclusion (modularFunctionFieldC_le_full κ (N * q))).toRingHom g) :=
    fun g => inclusion_symm_eq_symm_inclusion κ N q hM hs σ hσ τ hτ g
  apply SetLike.ext
  intro f
  simp only [ModularCurve.autOnPlaces, Place.congrEquiv_apply, Place.congrRingEquiv_toValuationSubring,
    ValuationSubring.mem_comap, hP]
  rw [key]

end S_WeierstrassCurve_exists_rationalHom_ker_eq_zmultiples_toValuationSubring_autOnPlaces_eq_comap_moduliPlace_map_sup_ker_nsmul
end P2MW
export P2MW.S_WeierstrassCurve_exists_rationalHom_ker_eq_zmultiples_toValuationSubring_autOnPlaces_eq_comap_moduliPlace_map_sup_ker_nsmul (solution)
