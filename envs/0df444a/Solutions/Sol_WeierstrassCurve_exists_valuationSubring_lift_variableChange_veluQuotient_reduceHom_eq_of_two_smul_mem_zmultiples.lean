-- Prove2me | solution 1 for WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5ff3dac6-9383-5875-9ad9-44cfe4a872ac

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_apply_twoTorsion_eq_of_smul_eq_veluQuotient
import Theorems.Thm_WeierstrassCurve_veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.kohelW_one Polynomial.rootESymm_zero_right WeierstrassCurve.kohelQuotient_a₂ WeierstrassCurve.kohelQuotient_a₃ WeierstrassCurve.kohelT_one WeierstrassCurve.kohelQuotient_one WeierstrassCurve.kohelQuotient_a₁ Polynomial.rootESymm_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.legendreVariableChange_s WeierstrassCurve.legendreVariableChange_t WeierstrassCurve.legendreVariableChange_r WeierstrassCurve.legendreVariableChange_u ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine Affine.negY Affine.Y_eq_of_Y_ne mk.injEq a₃ a₁ map map_b₂ b₂ mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.nonsingular_iff' Affine.Point.some.injEq reduction toAffine Affine.Point b₆ map_a₁ Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ VariableChange Affine.equation_iff natDegree_Ψ₂Sq Affine.Point.neg_some j b₄ map_a₃ reduceHom Affine.Y_mem_of_X_mem Affine.nonsingular_residue reducePoint reducePoint_some_of_mem Affine.vcX Affine.vcY Affine.vcXInv Affine.vcYInv Affine.vcX_vcXInv Affine.vcY_vcYInv Affine.nonsingular_variableChange_iff Affine.Point.vcFun Affine.Point.vcInvFun Affine.Point.vcFun_leftInverse Affine.Point.vcFun_rightInverse Affine.Point.equivOfVariableChangeEq ratPointMap_zero ratPointMap_some ratPointMap_injective ratPointHom ratPointMap veluGy veluU veluT_eq veluQuotient veluQuotient_b₂ veluX veluY Affine.Point.coordsOrZero Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet exists_valuationSubring_lift_variableChange_veluQuotient_apply_twoTorsion_eq_of_smul_eq_veluQuotient veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one Affine.Point.vcInvFun_add"
p2m_open "WeierstrassCurve"

namespace DeuringLevelTwo

section TwoTorsion

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
theorem eval_Ψ₂Sq (x : F) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_C, eval_pow, eval_X]

omit [DecidableEq F] in
theorem eval_derivative_Ψ₂Sq (x : F) :
    W.Ψ₂Sq.derivative.eval x = 12 * x ^ 2 + 2 * W.b₂ * x + 2 * W.b₄ := by
  simp only [Ψ₂Sq, derivative_add, derivative_mul, derivative_C, derivative_X_pow,
    derivative_X, zero_mul, zero_add, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    Nat.cast_ofNat, add_zero, mul_one]
  ring

omit [DecidableEq F] in

theorem equation_of_eval_Ψ₂Sq_eq_zero (h2 : (2 : F) ≠ 0) {x y : F} (hx : W.Ψ₂Sq.eval x = 0)
    (hy : y * 2 = -(W.a₁ * x + W.a₃)) : W.toAffine.Equation x y := by
  rw [Affine.equation_iff]
  change y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
  rw [eval_Ψ₂Sq] at hx
  simp only [b₂, b₄, b₆] at hx
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have key : y * 2 + (W.a₁ * x + W.a₃) = 0 := by rw [hy]; ring
  apply mul_left_cancel₀ h4
  linear_combination -1 * hx + (y * 2 + (W.a₁ * x + W.a₃)) * key

omit [DecidableEq F] in
theorem nonsingular_of_eval_Ψ₂Sq_eq_zero [W.IsElliptic] (h2 : (2 : F) ≠ 0) {x y : F}
    (hx : W.Ψ₂Sq.eval x = 0) (hy : y * 2 = -(W.a₁ * x + W.a₃)) : W.toAffine.Nonsingular x y :=
  (Affine.equation_iff_nonsingular).mp (equation_of_eval_Ψ₂Sq_eq_zero W h2 hx hy)

variable {W}

omit [DecidableEq F] in
private theorem some_congr {x₁ y₁ x₂ y₂ : F} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem two_smul_eq_zero_of_Y (h2 : (2 : F) ≠ 0) {x y : F} (h : W.toAffine.Nonsingular x y)
    (hy : y * 2 = -(W.a₁ * x + W.a₃)) : (2 : ℤ) • Affine.Point.some x y h = 0 := by
  rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some]
  refine some_congr rfl ?_ _ _
  simp only [Affine.negY]
  apply mul_left_cancel₀ h2
  linear_combination 2 * hy

theorem Y_mul_two_of_two_smul_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) : y * 2 = -(W.a₁ * x + W.a₃) := by
  rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at h2P
  have hy := h2P.2
  simp only [Affine.negY] at hy
  linear_combination hy

theorem eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) : W.Ψ₂Sq.eval x = 0 := by
  have hy := Y_mul_two_of_two_smul_eq_zero h h2P
  have heq := h.1
  rw [Affine.equation_iff] at heq
  rw [eval_Ψ₂Sq]
  simp only [b₂, b₄, b₆]
  have : (y * 2 + (W.a₁ * x + W.a₃)) ^ 2 = 0 := by rw [hy]; ring
  linear_combination -4 * heq + this

theorem eval_derivative_Ψ₂Sq_ne_zero_of_two_smul_eq_zero (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.toAffine.Nonsingular x y) (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) :
    W.Ψ₂Sq.derivative.eval x ≠ 0 := by
  have hy := Y_mul_two_of_two_smul_eq_zero h h2P
  have hns := (Affine.nonsingular_iff' x y).mp h
  rcases hns.2 with hX | hY
  · intro h0
    apply hX
    rw [eval_derivative_Ψ₂Sq] at h0
    simp only [b₂, b₄] at h0
    have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    change 4 * (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 4 * 0
    linear_combination -h0 + 2 * W.a₁ * hy
  · exfalso; apply hY
    change 2 * y + W.a₁ * x + W.a₃ = 0
    linear_combination hy

theorem eq_or_eq_neg_of_fst_eq' {x y y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x y') :
    Affine.Point.some x y' h' = Affine.Point.some x y h ∨
      Affine.Point.some x y' h' = -Affine.Point.some x y h := by
  by_cases hy : y' = W.toAffine.negY x y
  · right
    rw [Affine.Point.neg_some]
    exact some_congr rfl hy _ _
  · left
    have := Affine.Y_eq_of_Y_ne h'.left h.left rfl hy
    subst this
    rfl

theorem eq_of_fst_eq_of_two_smul_eq_zero {x y y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x y') (h2P : (2 : ℤ) • Affine.Point.some x y h = 0) :
    Affine.Point.some x y' h' = Affine.Point.some x y h := by
  by_cases hy : y' = W.toAffine.negY x y
  · have hneg : -Affine.Point.some x y h = Affine.Point.some x y h := by
      rw [two_zsmul, add_eq_zero_iff_eq_neg] at h2P; exact h2P.symm
    rw [← hneg, Affine.Point.neg_some]
    exact some_congr rfl hy _ _
  · have := Affine.Y_eq_of_Y_ne h'.left h.left rfl hy
    subst this
    rfl

omit [DecidableEq F] in

theorem eq_or_eq_or_eq_of_eval_Ψ₂Sq_eq_zero (h2 : (2 : F) ≠ 0) {x₁ x₂ x : F}
    (hx₁ : W.Ψ₂Sq.eval x₁ = 0) (hx₂ : W.Ψ₂Sq.eval x₂ = 0) (hx : x₁ ≠ x₂)
    (h0 : W.Ψ₂Sq.eval x = 0) : x = x₁ ∨ x = x₂ ∨ x = -W.b₂ / 4 - x₁ - x₂ := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [eval_Ψ₂Sq] at hx₁ hx₂ h0
  by_cases e1 : x = x₁
  · exact Or.inl e1
  by_cases e2 : x = x₂
  · exact Or.inr (Or.inl e2)
  right; right

  have hD1 : 4 * (x ^ 2 + x * x₁ + x₁ ^ 2) + W.b₂ * (x + x₁) + 2 * W.b₄ = 0 := by
    have : (x - x₁) * (4 * (x ^ 2 + x * x₁ + x₁ ^ 2) + W.b₂ * (x + x₁) + 2 * W.b₄) = 0 := by
      linear_combination h0 - hx₁
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr e1)
  have hD2 : 4 * (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2) + W.b₂ * (x₂ + x₁) + 2 * W.b₄ = 0 := by
    have : (x₂ - x₁) * (4 * (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2) + W.b₂ * (x₂ + x₁) + 2 * W.b₄) = 0 := by
      linear_combination hx₂ - hx₁
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hx))
  have hE : (x - x₂) * (4 * (x + x₂ + x₁) + W.b₂) = 0 := by linear_combination hD1 - hD2
  have hE' := (mul_eq_zero.mp hE).resolve_left (sub_ne_zero.mpr e2)
  field_simp
  linear_combination hE'

omit [DecidableEq F] in

theorem eval_Ψ₂Sq_third_eq_zero (h2 : (2 : F) ≠ 0) {x₁ x₂ : F}
    (hx₁ : W.Ψ₂Sq.eval x₁ = 0) (hx₂ : W.Ψ₂Sq.eval x₂ = 0) (hx : x₁ ≠ x₂) :
    W.Ψ₂Sq.eval (-W.b₂ / 4 - x₁ - x₂) = 0 := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [eval_Ψ₂Sq] at hx₁ hx₂ ⊢
  have hD2 : 4 * (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2) + W.b₂ * (x₂ + x₁) + 2 * W.b₄ = 0 := by
    have : (x₂ - x₁) * (4 * (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2) + W.b₂ * (x₂ + x₁) + 2 * W.b₄) = 0 := by
      linear_combination hx₂ - hx₁
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hx))
  field_simp
  linear_combination (16 : F) * hx₁ + (- 4 * W.b₂ - 32 * x₁ - 16 * x₂) * hD2

omit [DecidableEq F] in

theorem third_ne_of_eval_derivative_ne_zero (h2 : (2 : F) ≠ 0) {x₁ x₂ : F}
    (hx₁ : W.Ψ₂Sq.eval x₁ = 0) (hx₂ : W.Ψ₂Sq.eval x₂ = 0) (hx : x₁ ≠ x₂)
    (hd : W.Ψ₂Sq.derivative.eval x₁ ≠ 0) : -W.b₂ / 4 - x₁ - x₂ ≠ x₁ := by
  intro h3
  apply hd
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  rw [eval_Ψ₂Sq] at hx₁ hx₂
  rw [eval_derivative_Ψ₂Sq]
  have hD2 : 4 * (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2) + W.b₂ * (x₂ + x₁) + 2 * W.b₄ = 0 := by
    have : (x₂ - x₁) * (4 * (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2) + W.b₂ * (x₂ + x₁) + 2 * W.b₄) = 0 := by
      linear_combination hx₂ - hx₁
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hx))
  have h3' : W.b₂ = -4 * (2 * x₁ + x₂) := by
    field_simp at h3
    linear_combination -h3
  rw [h3'] at hD2 ⊢
  linear_combination hD2

theorem exists_twoTorsion_basis [IsAlgClosed F] [W.IsElliptic] (h2 : (2 : F) ≠ 0) :
    ∃ (x₁ y₁ x₂ y₂ : F) (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂),
      (2 : ℤ) • Affine.Point.some x₁ y₁ h₁ = 0 ∧ (2 : ℤ) • Affine.Point.some x₂ y₂ h₂ = 0 ∧
      x₁ ≠ x₂ := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hdeg : W.Ψ₂Sq.natDegree = 3 := W.natDegree_Ψ₂Sq h4
  have hdeg' : W.Ψ₂Sq.degree = 3 := by
    rw [degree_eq_natDegree (fun h0 => by rw [h0, natDegree_zero] at hdeg; exact absurd hdeg (by norm_num)), hdeg]
    rfl
  obtain ⟨x₁, hx₁⟩ := IsAlgClosed.exists_root W.Ψ₂Sq (by rw [hdeg']; decide)
  rw [IsRoot.def] at hx₁
  have hy : ∀ x : F, -(W.a₁ * x + W.a₃) / 2 * 2 = -(W.a₁ * x + W.a₃) := fun x =>
    div_mul_cancel₀ _ h2
  have h₁ : W.toAffine.Nonsingular x₁ (-(W.a₁ * x₁ + W.a₃) / 2) :=
    nonsingular_of_eval_Ψ₂Sq_eq_zero W h2 hx₁ (hy x₁)
  have hP₁ := two_smul_eq_zero_of_Y h2 h₁ (hy x₁)

  set q := W.Ψ₂Sq /ₘ (X - C x₁) with hq
  have hfac : (X - C x₁) * q = W.Ψ₂Sq := (mul_divByMonic_eq_iff_isRoot).mpr hx₁
  have hqdeg : q.degree = 2 := by
    have := congrArg degree hfac
    rw [degree_mul, degree_X_sub_C, hdeg'] at this

    have hq0 : q ≠ 0 := fun h0 => by rw [h0, degree_zero] at this; exact absurd this (by decide)
    rw [degree_eq_natDegree hq0] at this ⊢
    have : (1 + q.natDegree : WithBot ℕ) = (3 : ℕ) := by exact_mod_cast this
    have h13 : 1 + q.natDegree = 3 := by exact_mod_cast this
    have : q.natDegree = 2 := by omega
    rw [this]; rfl
  obtain ⟨x₂, hx₂⟩ := IsAlgClosed.exists_root q (by rw [hqdeg]; decide)
  rw [IsRoot.def] at hx₂
  have hx₂' : W.Ψ₂Sq.eval x₂ = 0 := by rw [← hfac, eval_mul, hx₂, mul_zero]
  have hne : x₁ ≠ x₂ := by
    intro h12
    subst h12
    apply eval_derivative_Ψ₂Sq_ne_zero_of_two_smul_eq_zero h2 h₁ hP₁
    rw [← hfac, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      eval_add, eval_mul, hx₂, eval_sub, eval_X, eval_C, sub_self, zero_mul, zero_add]
  have h₂ : W.toAffine.Nonsingular x₂ (-(W.a₁ * x₂ + W.a₃) / 2) :=
    nonsingular_of_eval_Ψ₂Sq_eq_zero W h2 hx₂' (hy x₂)
  exact ⟨x₁, _, x₂, _, h₁, h₂, hP₁, two_smul_eq_zero_of_Y h2 h₂ (hy x₂), hne⟩

theorem eq_zero_of_two_smul_eq_zero_of_mem_zmultiples {G : Type*} [AddCommGroup G] {Q T : G} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) (hT : T ∈ AddSubgroup.zmultiples Q) (h2 : (2 : ℤ) • T = 0) :
    T = 0 := by
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT
  have h1 : (2 * j) • Q = 0 := by rw [mul_zsmul, h2]
  have h2' : ((2 * n + 1 : ℕ) : ℤ) ∣ 2 * j := by
    rw [← hQ]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr h1
  have hcop : IsCoprime ((2 * n + 1 : ℕ) : ℤ) 2 := by
    refine ⟨1, -(n : ℤ), ?_⟩; push_cast; ring
  have h3 : ((2 * n + 1 : ℕ) : ℤ) ∣ j := hcop.dvd_of_dvd_mul_left h2'
  obtain ⟨c, rfl⟩ := h3
  rw [mul_comm, mul_zsmul, natCast_zsmul, ← hQ, addOrderOf_nsmul_eq_zero, zsmul_zero]

theorem exists_two_smul_eq_zero_add_of_two_smul_mem {G : Type*} [AddCommGroup G] {Q P : G} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) (hP : (2 : ℤ) • P ∈ AddSubgroup.zmultiples Q) :
    ∃ T R : G, R ∈ AddSubgroup.zmultiples Q ∧ (2 : ℤ) • T = 0 ∧ P = T + R := by
  set Z := (2 : ℤ) • P with hZ
  refine ⟨P - (n + 1) • Z, (n + 1) • Z, AddSubgroup.nsmul_mem _ hP _, ?_, by abel⟩
  have hmZ : (2 * n + 1) • Z = 0 := by
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
    rw [← hj, ← natCast_zsmul, smul_comm, natCast_zsmul, ← hQ, addOrderOf_nsmul_eq_zero, zsmul_zero]
  have h2Z : (2 : ℤ) • ((n + 1) • Z) = Z := by
    rw [← natCast_zsmul, ← mul_zsmul, show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) = ((2 * n + 1 : ℕ) : ℤ) + 1 by
      push_cast; ring, add_zsmul, one_zsmul, natCast_zsmul, hmZ, zero_add]
  rw [zsmul_sub, h2Z, ← hZ, sub_self]

end TwoTorsion

theorem veluX_map {F K : Type*} [Field F] [Field K] [DecidableEq K] (f : F →+* K)
    (W : WeierstrassCurve F) (S : Finset (F × F)) (x : F) :
    (W.map f).veluX (S.image (Prod.map f f)) (f x) = f (W.veluX S x) := by
  rw [veluX, veluX, Finset.sum_image ((f.injective.prodMap f.injective).injOn), map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [Prod.map_fst, Prod.map_snd, veluT_eq, veluU, veluGy, map_b₂, map_b₄, map_a₁, map_a₃,
    map_add, map_div₀, map_mul, map_pow, map_sub, map_neg, map_ofNat]

section VC

variable {F : Type*} [Field F] [DecidableEq F]

theorem vcFun_add (C : VariableChange F) (W : WeierstrassCurve.Affine F)
    (P Q : (C • W).toAffine.Point) :
    Affine.Point.vcFun C W (P + Q) = Affine.Point.vcFun C W P + Affine.Point.vcFun C W Q := by
  obtain ⟨P', rfl⟩ : ∃ P', P = Affine.Point.vcInvFun C W P' :=
    ⟨Affine.Point.vcFun C W P, (Affine.Point.vcFun_leftInverse P).symm⟩
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Affine.Point.vcInvFun C W Q' :=
    ⟨Affine.Point.vcFun C W Q, (Affine.Point.vcFun_leftInverse Q).symm⟩
  rw [← Affine.Point.vcInvFun_add, Affine.Point.vcFun_rightInverse, Affine.Point.vcFun_rightInverse,
    Affine.Point.vcFun_rightInverse]

theorem equivOfVariableChangeEq_add {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (P Q : Y.toAffine.Point) :
    Affine.Point.equivOfVariableChangeEq h (P + Q) =
      Affine.Point.equivOfVariableChangeEq h P + Affine.Point.equivOfVariableChangeEq h Q := by
  subst h; exact vcFun_add C X P Q

noncomputable def eqvHom {C : VariableChange F} {X Y : WeierstrassCurve.Affine F} (h : C • X = Y) :
    Y.toAffine.Point →+ X.toAffine.Point where
  toFun := Affine.Point.equivOfVariableChangeEq h
  map_zero' := by subst h; rfl
  map_add' := equivOfVariableChangeEq_add h

theorem eqvHom_apply {C : VariableChange F} {X Y : WeierstrassCurve.Affine F} (h : C • X = Y)
    (P : Y.toAffine.Point) : eqvHom h P = Affine.Point.equivOfVariableChangeEq h P := rfl

noncomputable def eqvSymmHom {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) : X.toAffine.Point →+ Y.toAffine.Point where
  toFun := (Affine.Point.equivOfVariableChangeEq h).symm
  map_zero' := by
    rw [Equiv.symm_apply_eq]; exact (map_zero (eqvHom h)).symm
  map_add' P Q := by
    rw [Equiv.symm_apply_eq]
    show P + Q = eqvHom h _
    rw [map_add, eqvHom_apply, eqvHom_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem eqvSymmHom_apply {C : VariableChange F} {X Y : WeierstrassCurve.Affine F} (h : C • X = Y)
    (P : X.toAffine.Point) :
    eqvSymmHom h P = (Affine.Point.equivOfVariableChangeEq h).symm P := rfl

theorem addOrderOf_equivOfVariableChangeEq {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (P : Y.toAffine.Point) :
    addOrderOf (Affine.Point.equivOfVariableChangeEq h P) = addOrderOf P := by
  rw [← eqvHom_apply]
  exact addOrderOf_injective (eqvHom h) (Affine.Point.equivOfVariableChangeEq h).injective P

theorem nsmul_equivOfVariableChangeEq {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (P : Y.toAffine.Point) (j : ℕ) :
    j • Affine.Point.equivOfVariableChangeEq h P = Affine.Point.equivOfVariableChangeEq h (j • P) := by
  rw [← eqvHom_apply, ← eqvHom_apply, map_nsmul]

theorem equivOfVariableChangeEq_some {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (x y : F) (hxy : Y.toAffine.Nonsingular x y) :
    ∃ hxy', Affine.Point.equivOfVariableChangeEq h (.some x y hxy) =
      .some (Affine.vcX C x) (Affine.vcY C x y) hxy' := by
  subst h; exact ⟨_, rfl⟩

theorem equivOfVariableChangeEq_symm_some {C : VariableChange F} {X Y : WeierstrassCurve.Affine F}
    (h : C • X = Y) (x y : F) (hxy : X.toAffine.Nonsingular x y) :
    ∃ hxy', (Affine.Point.equivOfVariableChangeEq h).symm (.some x y hxy) =
      .some (Affine.vcXInv C x) (Affine.vcYInv C x y) hxy' := by
  subst h; exact ⟨_, rfl⟩

theorem coordsOrZero_equivOfVariableChangeEq_one {X Y : WeierstrassCurve.Affine F}
    (h : (1 : VariableChange F) • X = Y) (P : Y.toAffine.Point) :
    (Affine.Point.equivOfVariableChangeEq h P).coordsOrZero = P.coordsOrZero := by
  rcases P with _ | ⟨x, y, hxy⟩
  · show (Affine.Point.equivOfVariableChangeEq h 0).coordsOrZero = (0 : Y.toAffine.Point).coordsOrZero
    rw [← eqvHom_apply, map_zero]
    rfl
  · obtain ⟨hxy', e⟩ := equivOfVariableChangeEq_some h x y hxy
    rw [e, Affine.Point.coordsOrZero_some, Affine.Point.coordsOrZero_some]
    simp only [Affine.vcX, Affine.vcY]
    ext
    · show ((1 : Fˣ) : F) ^ 2 * x + 0 = x
      simp
    · show ((1 : Fˣ) : F) ^ 3 * y + ((1 : Fˣ) : F) ^ 2 * 0 * x + 0 = y
      simp

theorem oddOrderSummingSet_equivOfVariableChangeEq_one {X Y : WeierstrassCurve.Affine F}
    (h : (1 : VariableChange F) • X = Y) (P : Y.toAffine.Point) (n : ℕ) :
    X.oddOrderSummingSet (Affine.Point.equivOfVariableChangeEq h P) n = Y.oddOrderSummingSet P n := by
  simp only [oddOrderSummingSet, nsmul_equivOfVariableChangeEq,
    coordsOrZero_equivOfVariableChangeEq_one]

noncomputable def vcInvHom (C : VariableChange F) (W : WeierstrassCurve F) :
    W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := Affine.Point.vcInvFun C W
  map_zero' := rfl
  map_add' := Affine.Point.vcInvFun_add C W

end VC

section RatPoint

variable {F K : Type} [Field F] [Field K] [DecidableEq F] [DecidableEq K] (f : F →+* K)
  {W : WeierstrassCurve F}

theorem coordsOrZero_ratPointHom (P : W.toAffine.Point) :
    (ratPointHom f P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show (ratPointMap f (0 : W.toAffine.Point)).coordsOrZero = _
    rw [ratPointMap_zero]
    simp [Affine.Point.coordsOrZero]
  · show (ratPointMap f (.some x y h)).coordsOrZero = _
    rw [ratPointMap_some]
    rfl

theorem oddOrderSummingSet_ratPointHom (Q : W.toAffine.Point) (n : ℕ) :
    (W.map f).oddOrderSummingSet (ratPointHom f Q) n =
      (W.oddOrderSummingSet Q n).image (Prod.map f f) := by
  simp only [oddOrderSummingSet, Finset.image_image]
  congr 1
  funext k
  simp only [Function.comp_apply, ← map_nsmul, coordsOrZero_ratPointHom]

end RatPoint

open scoped Classical in
theorem main
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h2 : (2 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : WeierstrassCurve.VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra (FractionRing (WittVector p k)) Ω]
    [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] :
    ∃ (B : ValuationSubring Ω) (φ : k ≃+* IsLocalRing.ResidueField B) (E' : WeierstrassCurve B)
      (_ : E'.IsElliptic) (hΔ' : (E'.map (IsLocalRing.residue B)).Δ ≠ 0)
      (v' : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B))
      (hv' : v' • E'.map (IsLocalRing.residue B) = W.map φ.toRingHom)
      (Q' : (E'.map B.subtype).toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1)
      (_ : WeierstrassCurve.ratPointHom φ.toRingHom Q₀ =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' Q'))
      (γ : WeierstrassCurve.VariableChange Ω)
      (hγ : γ • E'.map B.subtype =
        (E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n)),
      ∀ (x' y' : Ω) (h' : (E'.map B.subtype).toAffine.Nonsingular x' y')
        (x y : k) (h : W.toAffine.Nonsingular x y),
        (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
          ∈ AddSubgroup.zmultiples Q₀ →
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x' y' h' : (E'.map B.subtype).toAffine.Point)
          ∈ AddSubgroup.zmultiples Q' →
        WeierstrassCurve.ratPointHom φ.toRingHom (.some x y h) =
          (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
            (WeierstrassCurve.reduceHom hΔ' (.some x' y' h')) →
        ∃ (h'' : ((E'.map B.subtype).veluQuotient
              ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular
              ((E'.map B.subtype).veluX ((E'.map B.subtype).oddOrderSummingSet Q' n) x')
              ((E'.map B.subtype).veluY ((E'.map B.subtype).oddOrderSummingSet Q' n) x' y'))
          (h₀'' : (W.veluQuotient (W.oddOrderSummingSet Q₀ n)).toAffine.Nonsingular
              (W.veluX (W.oddOrderSummingSet Q₀ n) x) (W.veluY (W.oddOrderSummingSet Q₀ n) x y)),
          WeierstrassCurve.ratPointHom φ.toRingHom
              (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ₀ (.some _ _ h₀'')) =
            (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
              (WeierstrassCurve.reduceHom hΔ'
                (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ (.some _ _ h''))) := by
  classical
  have h4k : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2

  obtain ⟨x₁, y₁, x₂, y₂, h₁, h₂, hP₁, hP₂, hx12⟩ := exists_twoTorsion_basis (W := W) h2
  obtain ⟨B, φ, E', hE'ell, hΔ', hv', Q', hQ'ord, hRQ, γ, hγ, e₁, e₂, t₁, t₂, hT₁, hT₂, e'₁, e'₂,
      t'₁, t'₂, hT'₁, hT'₂, h2T₁, h2T₂, hR₁, hR₂, hγ₁, hγ₂, hr₁, hr₂⟩ :=
    exists_valuationSubring_lift_variableChange_veluQuotient_apply_twoTorsion_eq_of_smul_eq_veluQuotient
      p h2 W n hm hsq Q₀ hQ₀ γ₀ hγ₀ h₁ h₂ hP₁ hP₂ hx12 Ω
  haveI := hE'ell
  refine ⟨B, φ, E', hE'ell, hΔ', 1, hv', Q', hQ'ord, hRQ, γ, hγ, ?_⟩
  intro x' y' h' x y h h2P hnot h2P' hred

  let S₀ := W.oddOrderSummingSet Q₀ n
  let EΩ : WeierstrassCurve Ω := E'.map B.subtype
  let S' := EΩ.oddOrderSummingSet Q' n
  let Vq : WeierstrassCurve Ω := EΩ.veluQuotient S'
  let μ : W.toAffine.Point →+ (W.map φ.toRingHom).toAffine.Point := ratPointHom φ.toRingHom
  let ν : EΩ.toAffine.Point →+ (W.map φ.toRingHom).toAffine.Point :=
    (eqvSymmHom hv').comp (reduceHom hΔ')
  have hν : ∀ P, ν P = (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' P) :=
    fun P => rfl
  have hμinj : Function.Injective μ := fun a b hab => ratPointMap_injective φ.toRingHom hab
  have hEW : E'.map (residue B) = W.map φ.toRingHom := by rw [← hv', one_smul]
  have h2B : (2 : ResidueField B) ≠ 0 := by rw [← map_ofNat φ 2]; exact (map_ne_zero φ).mpr h2
  have h4B : (4 : ResidueField B) ≠ 0 := by rw [← map_ofNat φ 4]; exact (map_ne_zero φ).mpr h4k
  have hmB : ((2 * n + 1 : ℕ) : ResidueField B) ≠ 0 := by
    rw [← map_natCast φ]; exact (map_ne_zero φ).mpr hm
  have h2Ω : (2 : Ω) ≠ 0 := two_ne_zero
  have hmΩ : ((2 * n + 1 : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hb₂ : residue B E'.b₂ = φ W.b₂ := by
    have := congrArg WeierstrassCurve.b₂ hEW
    rwa [map_b₂, map_b₂] at this
  have hEΩb₂ : EΩ.b₂ = ((E'.b₂ : B) : Ω) := map_b₂ E' B.subtype
  have hVqb₂ : Vq.b₂ = ((E'.b₂ : B) : Ω) := by rw [← hEΩb₂]; exact veluQuotient_b₂ EΩ S'
  have hγ₀b₂ : (γ₀ • W).b₂ = W.b₂ := by rw [hγ₀, veluQuotient_b₂]
  haveI : EΩ.IsElliptic := inferInstance

  have hRED : ∀ (f : B) (t : Ω) (hT : EΩ.toAffine.Nonsingular f t),
      ∃ yy hh, ν (.some (f : Ω) t hT) = .some (residue B f) yy hh := by
    intro f t hT
    have hfmem : (f : Ω) ∈ B := f.2
    have hred1 : reduceHom hΔ' (.some (f : Ω) t hT) = reducePoint hΔ' (.some (f : Ω) t hT) := rfl
    rw [hν, hred1, reducePoint_some_of_mem hΔ' hT hfmem]
    obtain ⟨hxy', e⟩ := equivOfVariableChangeEq_symm_some hv'
      (residue B ⟨(f : Ω), hfmem⟩) (residue B ⟨t, Affine.Y_mem_of_X_mem E' hT.1 hfmem⟩)
      (Affine.nonsingular_residue E' hΔ' hT.1)
    rw [e]
    have hff : (⟨(f : Ω), hfmem⟩ : B) = f := Subtype.ext rfl
    have hxeq : Affine.vcXInv (1 : VariableChange (ResidueField B)) (residue B ⟨(f : Ω), hfmem⟩) =
        residue B f := by
      rw [hff]
      show (((1 : (ResidueField B)ˣ)⁻¹ : (ResidueField B)ˣ) : ResidueField B) ^ 2 *
        (residue B f - 0) = residue B f
      simp
    have hh : (W.map φ.toRingHom).toAffine.Nonsingular (residue B f)
        (Affine.vcYInv (1 : VariableChange (ResidueField B)) (residue B ⟨(f : Ω), hfmem⟩)
          (residue B ⟨t, Affine.Y_mem_of_X_mem E' hT.1 hfmem⟩)) := by
      have := hxy'; rw [hxeq] at this; exact this
    exact ⟨_, hh, some_congr hxeq rfl _ _⟩
  have hμsome : ∀ (a b : k) (hab : W.toAffine.Nonsingular a b),
      μ (.some a b hab) = .some (φ a) (φ b)
        (((W.toAffine.map_nonsingular φ.toRingHom.injective a b).mpr hab)) := fun a b hab => rfl

  have hres_of : ∀ {a b : k} (hab : W.toAffine.Nonsingular a b) {f : B} {t : Ω}
      (hT : EΩ.toAffine.Nonsingular f t), μ (.some a b hab) = ν (.some (f : Ω) t hT) →
      residue B f = φ a := by
    intro a b hab f t hT hR
    obtain ⟨yy, hh, e⟩ := hRED f t hT
    rw [e, hμsome] at hR
    exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp hR).1.symm
  have hre₁ : residue B e₁ = φ x₁ := hres_of h₁ hT₁ hR₁
  have hre₂ : residue B e₂ = φ x₂ := hres_of h₂ hT₂ hR₂

  have hΨx₁ := eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero h₁ hP₁
  have hΨx₂ := eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero h₂ hP₂
  set x₃ : k := -W.b₂ / 4 - x₁ - x₂ with hx₃_def
  have hΨx₃ : W.Ψ₂Sq.eval x₃ = 0 := eval_Ψ₂Sq_third_eq_zero h2 hΨx₁ hΨx₂ hx12
  have hx31 : x₃ ≠ x₁ := third_ne_of_eval_derivative_ne_zero h2 hΨx₁ hΨx₂ hx12
    (eval_derivative_Ψ₂Sq_ne_zero_of_two_smul_eq_zero h2 h₁ hP₁)
  have hx32 : x₃ ≠ x₂ := by
    have := third_ne_of_eval_derivative_ne_zero h2 hΨx₂ hΨx₁ (Ne.symm hx12)
      (eval_derivative_Ψ₂Sq_ne_zero_of_two_smul_eq_zero h2 h₂ hP₂)
    intro h32; apply this; rw [hx₃_def] at h32; linear_combination h32
  have hy₃ : -(W.a₁ * x₃ + W.a₃) / 2 * 2 = -(W.a₁ * x₃ + W.a₃) := div_mul_cancel₀ _ h2
  have h₃ : W.toAffine.Nonsingular x₃ (-(W.a₁ * x₃ + W.a₃) / 2) :=
    nonsingular_of_eval_Ψ₂Sq_eq_zero W h2 hΨx₃ hy₃
  have hP₃ := two_smul_eq_zero_of_Y h2 h₃ hy₃

  set x'₁ := Affine.vcXInv γ₀ x₁ with hx'₁
  set x'₂ := Affine.vcXInv γ₀ x₂ with hx'₂
  set x'₃ : k := -W.b₂ / 4 - x'₁ - x'₂ with hx'₃_def
  have hvcinj : Function.Injective (Affine.vcXInv γ₀) := fun a b hab => by
    rw [← Affine.vcX_vcXInv (C := γ₀) a, ← Affine.vcX_vcXInv (C := γ₀) b]; exact congrArg _ hab
  have hx'12 : x'₁ ≠ x'₂ := fun h12 => hx12 (hvcinj h12)
  have hΨ' : ∀ {a b : k} (hab : W.toAffine.Nonsingular a b) (h2P : (2 : ℤ) • Affine.Point.some a b hab = 0),
      (γ₀ • W).Ψ₂Sq.eval (Affine.vcXInv γ₀ a) = 0 := by
    intro a b hab h2P
    have hT : vcInvHom γ₀ W (Affine.Point.some a b hab) =
        Affine.Point.some (Affine.vcXInv γ₀ a) (Affine.vcYInv γ₀ a b)
          ((Affine.nonsingular_variableChange_iff _ _).mpr
            (by rwa [Affine.vcX_vcXInv, Affine.vcY_vcYInv])) := rfl
    have h2T : (2 : ℤ) • vcInvHom γ₀ W (Affine.Point.some a b hab) = 0 := by
      rw [← map_zsmul, h2P, map_zero]
    rw [hT] at h2T
    exact eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero _ h2T
  have hx'₃ : Affine.vcXInv γ₀ x₃ = x'₃ := by
    rcases eq_or_eq_or_eq_of_eval_Ψ₂Sq_eq_zero (W := γ₀ • W) h2 (hΨ' h₁ hP₁) (hΨ' h₂ hP₂) hx'12
      (hΨ' h₃ hP₃) with e | e | e
    · exact absurd (hvcinj e) hx31
    · exact absurd (hvcinj e) hx32
    · rw [e, hγ₀b₂]

  have hΨe₁ : EΩ.Ψ₂Sq.eval (e₁ : Ω) = 0 := eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero hT₁ h2T₁
  have hΨe₂ : EΩ.Ψ₂Sq.eval (e₂ : Ω) = 0 := eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero hT₂ h2T₂
  have he12 : (e₁ : Ω) ≠ e₂ := by
    intro h12
    apply hx12
    have := congrArg (residue B) (Subtype.ext h12 : e₁ = e₂)
    rw [hre₁, hre₂] at this
    exact φ.injective this

  have hthird : ∀ (bB f₁ f₂ : B) (zb z₁ z₂ : k), residue B bB = φ zb → residue B f₁ = φ z₁ →
      residue B f₂ = φ z₂ → ∃ f₃ : B, (f₃ : Ω) = -(bB : Ω) / 4 - f₁ - f₂ ∧
        residue B f₃ = φ (-zb / 4 - z₁ - z₂) := by
    intro bB f₁ f₂ zb z₁ z₂ hb hf₁ hf₂
    have h4u : IsUnit (4 : B) := (residue_ne_zero_iff_isUnit _).mp (by rw [map_ofNat]; exact h4B)
    let i4 : B := ↑(h4u.unit⁻¹)
    have h4i : (4 : B) * i4 = 1 := by
      show (h4u.unit : B) * ↑(h4u.unit⁻¹) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hi4Ω : (i4 : Ω) = 4⁻¹ := by
      have h1 : ((4 : B) : Ω) * (i4 : Ω) = 1 := by exact_mod_cast congrArg Subtype.val h4i
      push_cast at h1
      exact eq_inv_of_mul_eq_one_right h1
    have hi4r : residue B i4 = 4⁻¹ := by
      have h1 : residue B 4 * residue B i4 = 1 := by rw [← map_mul, h4i, map_one]
      rw [map_ofNat] at h1
      exact eq_inv_of_mul_eq_one_right h1
    have hc4 : ((4 : B) : Ω) = 4 := map_ofNat B.subtype 4
    refine ⟨(-bB - 4 * f₁ - 4 * f₂) * i4, ?_, ?_⟩
    · push_cast
      rw [hi4Ω, hc4]
      field_simp
    · rw [map_mul, map_sub, map_sub, map_neg, map_mul, map_mul, map_ofNat, hi4r, hb, hf₁, hf₂,
        ← map_ofNat φ 4, ← map_mul, ← map_mul, ← map_neg, ← map_sub, ← map_sub, ← map_inv₀,
        ← map_mul]
      congr 1
      field_simp
  obtain ⟨e₃, he₃Ω, hre₃⟩ := hthird E'.b₂ e₁ e₂ W.b₂ x₁ x₂ hb₂ hre₁ hre₂
  have he₃Ω' : (e₃ : Ω) = -EΩ.b₂ / 4 - e₁ - e₂ := by rw [hEΩb₂]; exact he₃Ω
  have hΨe₃ : EΩ.Ψ₂Sq.eval (e₃ : Ω) = 0 := by
    rw [he₃Ω']; exact eval_Ψ₂Sq_third_eq_zero h2Ω hΨe₁ hΨe₂ he12
  have hty : ∀ (X : WeierstrassCurve Ω) (z : Ω), -(X.a₁ * z + X.a₃) / 2 * 2 = -(X.a₁ * z + X.a₃) :=
    fun X z => div_mul_cancel₀ _ h2Ω
  have hT₃ : EΩ.toAffine.Nonsingular (e₃ : Ω) (-(EΩ.a₁ * e₃ + EΩ.a₃) / 2) :=
    nonsingular_of_eval_Ψ₂Sq_eq_zero EΩ h2Ω hΨe₃ (hty _ _)
  have h2T₃ := two_smul_eq_zero_of_Y h2Ω hT₃ (hty _ _)
  have hR₃ : μ (.some x₃ _ h₃) = ν (.some (e₃ : Ω) _ hT₃) := by
    obtain ⟨yy, hh, e⟩ := hRED e₃ _ hT₃
    rw [e, hμsome]
    have h2L : (2 : ℤ) • μ (.some x₃ _ h₃) = 0 := by rw [← map_zsmul, hP₃, map_zero]
    rw [hμsome] at h2L
    clear e
    symm
    revert hh
    rw [hre₃, ← hx₃_def]
    intro hh
    exact eq_of_fst_eq_of_two_smul_eq_zero _ _ h2L
  have he31 : (e₃ : Ω) ≠ e₁ := by
    intro h31; apply hx31
    have := congrArg (residue B) (Subtype.ext h31 : e₃ = e₁)
    rw [hre₁, hre₃, ← hx₃_def] at this
    exact φ.injective this
  have he32 : (e₃ : Ω) ≠ e₂ := by
    intro h32; apply hx32
    have := congrArg (residue B) (Subtype.ext h32 : e₃ = e₂)
    rw [hre₂, hre₃, ← hx₃_def] at this
    exact φ.injective this

  have hU1 : ∀ U : EΩ.toAffine.Point, U ≠ 0 → (2 : ℤ) • U = 0 →
      ∃ (f : B) (t : Ω) (hU : EΩ.toAffine.Nonsingular f t) (xd yd : k)
        (hd : W.toAffine.Nonsingular xd yd), U = .some f t hU ∧
        (2 : ℤ) • Affine.Point.some xd yd hd = 0 ∧ μ (.some xd yd hd) = ν (.some f t hU) ∧
        residue B f = φ xd := by
    intro U hU0 h2U
    rcases U with _ | ⟨u, t, hut⟩
    · exact absurd rfl hU0
    have hΨu := eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero hut h2U
    rcases eq_or_eq_or_eq_of_eval_Ψ₂Sq_eq_zero (W := EΩ) h2Ω hΨe₁ hΨe₂ he12 hΨu with e | e | e
    · subst e
      exact ⟨e₁, t₁, hT₁, x₁, y₁, h₁, eq_of_fst_eq_of_two_smul_eq_zero hT₁ hut h2T₁, hP₁, hR₁, hre₁⟩
    · subst e
      exact ⟨e₂, t₂, hT₂, x₂, y₂, h₂, eq_of_fst_eq_of_two_smul_eq_zero hT₂ hut h2T₂, hP₂, hR₂, hre₂⟩
    · rw [← he₃Ω'] at e
      subst e
      exact ⟨e₃, _, hT₃, x₃, _, h₃, eq_of_fst_eq_of_two_smul_eq_zero hT₃ hut h2T₃, hP₃, hR₃, hre₃⟩

  have hγinj : Function.Injective (Affine.Point.equivOfVariableChangeEq hγ) :=
    (Affine.Point.equivOfVariableChangeEq hγ).injective
  have h2γ : ∀ P : Vq.toAffine.Point, (2 : ℤ) • Affine.Point.equivOfVariableChangeEq hγ P =
      Affine.Point.equivOfVariableChangeEq hγ ((2 : ℤ) • P) := fun P => by
    rw [← eqvHom_apply, ← eqvHom_apply, map_zsmul]
  have h2T'₁ : (2 : ℤ) • Affine.Point.some _ _ hT'₁ = 0 := by
    apply hγinj
    rw [← h2γ, hγ₁, h2T₁, ← eqvHom_apply, map_zero]
  have h2T'₂ : (2 : ℤ) • Affine.Point.some _ _ hT'₂ = 0 := by
    apply hγinj
    rw [← h2γ, hγ₂, h2T₂, ← eqvHom_apply, map_zero]
  have hΨe'₁ : Vq.Ψ₂Sq.eval (e'₁ : Ω) = 0 := eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero hT'₁ h2T'₁
  have hΨe'₂ : Vq.Ψ₂Sq.eval (e'₂ : Ω) = 0 := eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero hT'₂ h2T'₂
  have he'12 : (e'₁ : Ω) ≠ e'₂ := by
    intro h12
    apply hx'12
    have := congrArg (residue B) (Subtype.ext h12 : e'₁ = e'₂)
    rw [hr₁, hr₂] at this
    exact φ.injective this
  obtain ⟨e'₃, he'₃Ω, hre'₃⟩ := hthird E'.b₂ e'₁ e'₂ W.b₂ x'₁ x'₂ hb₂ hr₁ hr₂
  have he'₃Ω' : (e'₃ : Ω) = -Vq.b₂ / 4 - e'₁ - e'₂ := by rw [hVqb₂]; exact he'₃Ω

  have hU2 : ∀ U' : Vq.toAffine.Point, U' ≠ 0 → (2 : ℤ) • U' = 0 →
      ∃ (f' : B) (t' : Ω) (hU' : Vq.toAffine.Nonsingular f' t') (xd yd : k)
        (hd : W.toAffine.Nonsingular xd yd), U' = .some f' t' hU' ∧
        (2 : ℤ) • Affine.Point.some xd yd hd = 0 ∧
        μ (.some xd yd hd) = ν (Affine.Point.equivOfVariableChangeEq hγ U') ∧
        residue B f' = φ (Affine.vcXInv γ₀ xd) := by
    intro U' hU'0 h2U'
    set U := Affine.Point.equivOfVariableChangeEq hγ U' with hU_def
    have hU0 : U ≠ 0 := by
      intro h0; apply hU'0; apply hγinj
      rw [← hU_def, h0, ← eqvHom_apply, map_zero]
    have h2U : (2 : ℤ) • U = 0 := by rw [hU_def, h2γ, h2U', ← eqvHom_apply, map_zero]
    obtain ⟨f, t, hU, xd, yd, hd, hUeq, hd2, hdR, hfres⟩ := hU1 U hU0 h2U
    rcases U' with _ | ⟨u', s', hus'⟩
    · exact absurd rfl hU'0
    have hΨu' := eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero hus' h2U'
    rcases eq_or_eq_or_eq_of_eval_Ψ₂Sq_eq_zero (W := Vq) h2Ω hΨe'₁ hΨe'₂ he'12 hΨu' with e | e | e
    · subst e
      have hU'T : Affine.Point.some _ s' hus' = Affine.Point.some _ _ hT'₁ :=
        eq_of_fst_eq_of_two_smul_eq_zero hT'₁ hus' h2T'₁
      refine ⟨e'₁, t'₁, hT'₁, x₁, y₁, h₁, hU'T, hP₁, ?_, hr₁⟩
      rw [hU_def, hU'T, hγ₁]; exact hR₁
    · subst e
      have hU'T : Affine.Point.some _ s' hus' = Affine.Point.some _ _ hT'₂ :=
        eq_of_fst_eq_of_two_smul_eq_zero hT'₂ hus' h2T'₂
      refine ⟨e'₂, t'₂, hT'₂, x₂, y₂, h₂, hU'T, hP₂, ?_, hr₂⟩
      rw [hU_def, hU'T, hγ₂]; exact hR₂
    · rw [← he'₃Ω'] at e
      subst e

      have hf : (f : Ω) = e₃ := by
        have hΨf : EΩ.Ψ₂Sq.eval (f : Ω) = 0 := by
          rw [hUeq] at h2U; exact eval_Ψ₂Sq_eq_zero_of_two_smul_eq_zero hU h2U
        rcases eq_or_eq_or_eq_of_eval_Ψ₂Sq_eq_zero (W := EΩ) h2Ω hΨe₁ hΨe₂ he12 hΨf with e | e | e
        · exfalso
          have hU1 : EΩ.toAffine.Nonsingular (e₁ : Ω) t := by rw [← e]; exact hU
          have hUT : U = Affine.Point.some _ _ hT₁ := by
            rw [hUeq]
            exact (some_congr e rfl hU hU1).trans (eq_of_fst_eq_of_two_smul_eq_zero hT₁ hU1 h2T₁)
          have : Affine.Point.some (e'₃ : Ω) s' hus' = Affine.Point.some _ _ hT'₁ := by
            apply hγinj; rw [← hU_def, hUT, hγ₁]
          have h13 := ((Affine.Point.some.injEq _ _ _ _ _ _).mp this).1
          have hr := congrArg (residue B) (Subtype.ext h13 : e'₃ = e'₁)
          rw [hre'₃, hr₁] at hr
          have hr' := φ.injective hr
          apply hx31; apply hvcinj
          rw [hx'₃]; exact hr'
        · exfalso
          have hU2' : EΩ.toAffine.Nonsingular (e₂ : Ω) t := by rw [← e]; exact hU
          have hUT : U = Affine.Point.some _ _ hT₂ := by
            rw [hUeq]
            exact (some_congr e rfl hU hU2').trans (eq_of_fst_eq_of_two_smul_eq_zero hT₂ hU2' h2T₂)
          have : Affine.Point.some (e'₃ : Ω) s' hus' = Affine.Point.some _ _ hT'₂ := by
            apply hγinj; rw [← hU_def, hUT, hγ₂]
          have h23 := ((Affine.Point.some.injEq _ _ _ _ _ _).mp this).1
          have hr := congrArg (residue B) (Subtype.ext h23 : e'₃ = e'₂)
          rw [hre'₃, hr₂] at hr
          have hr' := φ.injective hr
          apply hx32; apply hvcinj
          rw [hx'₃]; exact hr'
        · rw [e, he₃Ω']
      have hU3 : EΩ.toAffine.Nonsingular (e₃ : Ω) t := by rw [← hf]; exact hU
      have hUT : U = Affine.Point.some _ _ hT₃ := by
        rw [hUeq]
        exact (some_congr hf rfl hU hU3).trans (eq_of_fst_eq_of_two_smul_eq_zero hT₃ hU3 h2T₃)
      refine ⟨e'₃, s', hus', x₃, _, h₃, rfl, hP₃, ?_, ?_⟩
      · rw [hUT]; exact hR₃
      · rw [hre'₃, hx'₃]

  obtain ⟨πk, hπk_ker, hπk⟩ :=
    exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one W n hm Q₀ hQ₀
  obtain ⟨πΩ, hπΩ_ker, hπΩ⟩ :=
    exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one EΩ n hmΩ Q' hQ'ord

  obtain ⟨T, R, hR, h2T, hPTR⟩ := exists_two_smul_eq_zero_add_of_two_smul_mem hQ₀ h2P
  obtain ⟨T', R', hR', h2T', hP'TR⟩ := exists_two_smul_eq_zero_add_of_two_smul_mem hQ'ord h2P'
  have hμQ : addOrderOf (μ Q₀) = 2 * n + 1 := (addOrderOf_injective μ hμinj Q₀).trans hQ₀
  have hνQ : ν Q' = μ Q₀ := by rw [hν]; exact hRQ.symm
  have hνR' : ν R' ∈ AddSubgroup.zmultiples (μ Q₀) := by
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR'
    rw [map_zsmul, hνQ]; exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _
  have hμR : μ R ∈ AddSubgroup.zmultiples (μ Q₀) := by
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
    rw [map_zsmul]; exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _
  have hpre : ∀ P : W.toAffine.Point, μ P ∈ AddSubgroup.zmultiples (μ Q₀) →
      P ∈ AddSubgroup.zmultiples Q₀ := by
    intro P hP
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
    rw [← map_zsmul] at hj
    rw [← hμinj hj]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _
  have hμT : μ T = ν T' := by
    have h1 : μ T - ν T' = ν R' - μ R := by
      have := hred
      change μ (Affine.Point.some x y h) = ν (Affine.Point.some x' y' h') at this
      rw [hPTR, hP'TR, map_add, map_add] at this
      linear_combination (norm := abel) this
    have hmem : μ T - ν T' ∈ AddSubgroup.zmultiples (μ Q₀) := by
      rw [h1]; exact AddSubgroup.sub_mem _ hνR' hμR
    have h2 : (2 : ℤ) • (μ T - ν T') = 0 := by
      rw [zsmul_sub, ← map_zsmul, ← map_zsmul, h2T, h2T', map_zero, map_zero, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_two_smul_eq_zero_of_mem_zmultiples hμQ hmem h2)
  have hT'0 : T' ≠ 0 := by
    intro h0
    apply hnot
    apply hpre
    change μ (Affine.Point.some x y h) ∈ _
    have := hred
    change μ (Affine.Point.some x y h) = ν (Affine.Point.some x' y' h') at this
    rw [this, hP'TR, h0, zero_add]
    exact hνR'
  have hP'not : (Affine.Point.some x' y' h' : EΩ.toAffine.Point) ∉ AddSubgroup.zmultiples Q' := by
    intro hmem
    apply hnot; apply hpre
    change μ (Affine.Point.some x y h) ∈ _
    have := hred
    change μ (Affine.Point.some x y h) = ν (Affine.Point.some x' y' h') at this
    rw [this]
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    rw [← hj, map_zsmul, hνQ]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _

  obtain ⟨f, t, hU, xd, yd, hd, hT'eq, hd2, hdR, hfres⟩ := hU1 T' hT'0 h2T'
  have hTd : T = Affine.Point.some xd yd hd := hμinj (by rw [hμT, hdR, hT'eq])
  have hd0 : (Affine.Point.some xd yd hd : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ := by
    intro hmem
    exact absurd (eq_zero_of_two_smul_eq_zero_of_mem_zmultiples hQ₀ hmem hd2)
      (Affine.Point.some_ne_zero _)
  have h2f : (2 : ℤ) • (Affine.Point.some (f : Ω) t hU : EΩ.toAffine.Point) = 0 := by
    rw [← hT'eq]; exact h2T'
  have hf0 : (Affine.Point.some (f : Ω) t hU : EΩ.toAffine.Point) ∉ AddSubgroup.zmultiples Q' := by
    intro hmem
    have := eq_zero_of_two_smul_eq_zero_of_mem_zmultiples hQ'ord hmem h2f
    exact absurd this (Affine.Point.some_ne_zero _)

  obtain ⟨h₀'', hπkP⟩ := hπk x y h hnot
  obtain ⟨hVd, hπkd⟩ := hπk xd yd hd hd0
  obtain ⟨h'', hπΩP⟩ := hπΩ x' y' h' hP'not
  obtain ⟨hUf, hπΩf⟩ := hπΩ (f : Ω) t hU hf0
  refine ⟨h'', h₀'', ?_⟩
  have hπkR : πk R = 0 := by rw [← AddMonoidHom.mem_ker, hπk_ker]; exact hR
  have hπΩR : πΩ R' = 0 := by rw [← AddMonoidHom.mem_ker, hπΩ_ker]; exact hR'
  have hLHS : (Affine.Point.some _ _ h₀'' : (W.veluQuotient S₀).toAffine.Point) =
      Affine.Point.some _ _ hVd := by
    rw [← hπkP, ← hπkd, ← hTd]
    show πk (Affine.Point.some x y h) = πk T
    rw [hPTR, map_add, hπkR, add_zero]
  have hRHS : (Affine.Point.some _ _ h'' : Vq.toAffine.Point) = Affine.Point.some _ _ hUf := by
    rw [← hπΩP, ← hπΩf, ← hT'eq]
    show πΩ (Affine.Point.some x' y' h') = πΩ T'
    rw [hP'TR, map_add, hπΩR, add_zero]
  rw [hLHS, hRHS]

  have h2U' : (2 : ℤ) • (Affine.Point.some _ _ hUf : Vq.toAffine.Point) = 0 := by
    rw [← hπΩf, ← map_zsmul, h2f, map_zero]
  obtain ⟨f', s', hU', xd', yd', hd', hU'eq, hd'2, hd'R, hf'res⟩ :=
    hU2 (Affine.Point.some _ _ hUf) (Affine.Point.some_ne_zero _) h2U'
  have hXf : EΩ.veluX S' (f : Ω) = (f' : Ω) :=
    ((Affine.Point.some.injEq _ _ _ _ _ _).mp hU'eq).1

  have hredQ' : reduceHom hΔ' Q' = Affine.Point.equivOfVariableChangeEq hv' (μ Q₀) := by
    rw [← Equiv.symm_apply_eq]; exact hRQ.symm
  have hordQ' : addOrderOf (reduceHom hΔ' Q') = 2 * n + 1 := by
    rw [hredQ', addOrderOf_equivOfVariableChangeEq, hμQ]
  have hSbar : (E'.map (residue B)).oddOrderSummingSet (reduceHom hΔ' Q') n =
      S₀.image (Prod.map φ.toRingHom φ.toRingHom) := by
    rw [hredQ', oddOrderSummingSet_equivOfVariableChangeEq_one, oddOrderSummingSet_ratPointHom]
  have hfmem : (f : Ω) ∈ B := f.2
  have hff : (⟨(f : Ω), hfmem⟩ : B) = f := Subtype.ext rfl
  have hx'S : ∀ P ∈ (E'.map (residue B)).oddOrderSummingSet (reduceHom hΔ' Q') n,
      P.1 ≠ residue B ⟨(f : Ω), hfmem⟩ := by
    intro P hP hP1
    rw [hSbar, Finset.mem_image] at hP
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hP
    rw [hff, hfres] at hP1
    have hax : a = xd := φ.injective hP1
    subst hax

    rw [mem_oddOrderSummingSet] at hab
    obtain ⟨j, hj1, hjn, hjQ⟩ := hab
    have hj0 : j • Q₀ ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ₀]; omega)
    apply hd0
    rcases hjQ' : j • Q₀ with _ | ⟨a', b', hab'⟩
    · exact absurd hjQ' hj0
    · rw [hjQ', Affine.Point.coordsOrZero_some, Prod.mk.injEq] at hjQ
      obtain ⟨rfl, rfl⟩ := hjQ
      have hjmem : (Affine.Point.some a' b' hab' : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q₀ := by
        rw [← hjQ']; exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _
      rcases eq_or_eq_neg_of_fst_eq' hab' hd with e | e
      · rw [e]; exact hjmem
      · rw [e]; exact AddSubgroup.neg_mem _ hjmem
  obtain ⟨hXmem, hG⟩ :=
    veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue hΔ' hmB Q' hQ'ord hordQ' hfmem hx'S

  have hG1 : residue B ⟨EΩ.veluX S' (f : Ω), hXmem⟩ = φ (Affine.vcXInv γ₀ xd') := by
    rw [← hf'res]
    exact congrArg (residue B) (Subtype.ext hXf)
  have hG2 : (E'.map (residue B)).veluX
      ((E'.map (residue B)).oddOrderSummingSet (reduceHom hΔ' Q') n) (residue B ⟨(f : Ω), hfmem⟩) =
      φ (W.veluX S₀ xd) := by
    rw [hSbar, hff, hfres, hEW]
    exact veluX_map φ.toRingHom W S₀ xd
  have hE1 : W.veluX S₀ xd = Affine.vcXInv γ₀ xd' :=
    φ.injective (hG2.symm.trans (hG.symm.trans hG1))

  obtain ⟨hns, hL⟩ := equivOfVariableChangeEq_some hγ₀ (W.veluX S₀ xd) (W.veluY S₀ xd yd) hVd
  have hxx : Affine.vcX γ₀ (W.veluX S₀ xd) = xd' := by rw [hE1, Affine.vcX_vcXInv]
  have hns' : W.toAffine.Nonsingular xd' (Affine.vcY γ₀ (W.veluX S₀ xd) (W.veluY S₀ xd yd)) := by
    rw [← hxx]; exact hns
  have hL' : Affine.Point.equivOfVariableChangeEq hγ₀ (Affine.Point.some _ _ hVd) =
      Affine.Point.some xd' yd' hd' := by
    rw [hL]
    exact (some_congr hxx rfl hns hns').trans (eq_of_fst_eq_of_two_smul_eq_zero hd' hns' hd'2)
  rw [hL']
  exact hd'R

end DeuringLevelTwo

end WeierstrassCurve

open scoped Classical in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h2 : (2 : k) ≠ 0)
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : WeierstrassCurve.VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra (FractionRing (WittVector p k)) Ω]
    [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] :
    ∃ (B : ValuationSubring Ω) (φ : k ≃+* IsLocalRing.ResidueField B) (E' : WeierstrassCurve B)
      (_ : E'.IsElliptic) (hΔ' : (E'.map (IsLocalRing.residue B)).Δ ≠ 0)
      (v' : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B))
      (hv' : v' • E'.map (IsLocalRing.residue B) = W.map φ.toRingHom)
      (Q' : (E'.map B.subtype).toAffine.Point) (_ : addOrderOf Q' = 2 * n + 1)
      (_ : WeierstrassCurve.ratPointHom φ.toRingHom Q₀ =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' Q'))
      (γ : WeierstrassCurve.VariableChange Ω)
      (hγ : γ • E'.map B.subtype =
        (E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n)),
      ∀ (x' y' : Ω) (h' : (E'.map B.subtype).toAffine.Nonsingular x' y')
        (x y : k) (h : W.toAffine.Nonsingular x y),
        (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
          ∈ AddSubgroup.zmultiples Q₀ →
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x' y' h' : (E'.map B.subtype).toAffine.Point)
          ∈ AddSubgroup.zmultiples Q' →
        WeierstrassCurve.ratPointHom φ.toRingHom (.some x y h) =
          (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
            (WeierstrassCurve.reduceHom hΔ' (.some x' y' h')) →
        ∃ (h'' : ((E'.map B.subtype).veluQuotient
              ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Nonsingular
              ((E'.map B.subtype).veluX ((E'.map B.subtype).oddOrderSummingSet Q' n) x')
              ((E'.map B.subtype).veluY ((E'.map B.subtype).oddOrderSummingSet Q' n) x' y'))
          (h₀'' : (W.veluQuotient (W.oddOrderSummingSet Q₀ n)).toAffine.Nonsingular
              (W.veluX (W.oddOrderSummingSet Q₀ n) x) (W.veluY (W.oddOrderSummingSet Q₀ n) x y)),
          WeierstrassCurve.ratPointHom φ.toRingHom
              (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ₀ (.some _ _ h₀'')) =
            (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
              (WeierstrassCurve.reduceHom hΔ'
                (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ (.some _ _ h''))) :=
  WeierstrassCurve.DeuringLevelTwo.main p h2 W n hm hsq Q₀ hQ₀ γ₀ hγ₀ Ω

end S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples
end P2MW
export P2MW.S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples (solution)
