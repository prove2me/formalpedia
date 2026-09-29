-- Prove2me | solution 1 for WeierstrassCurve.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/13953da0-6267-5bab-b392-f9da956ae388

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient
import Theorems.Thm_WeierstrassCurve_veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue
import Theorems.Thm_WeierstrassCurve_veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_mul_Psi3_add_mul_derivative_Psi3
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.kohelW_one Polynomial.rootESymm_zero_right WeierstrassCurve.kohelQuotient_a₂ WeierstrassCurve.kohelQuotient_a₃ WeierstrassCurve.kohelT_one WeierstrassCurve.kohelQuotient_one WeierstrassCurve.kohelQuotient_a₁ Polynomial.rootESymm_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.deuringVariableChange_s WeierstrassCurve.deuringVariableChange_t WeierstrassCurve.deuringCurve_a₄ WeierstrassCurve.deuringCurve_a₂ WeierstrassCurve.deuringCurve_a₆ WeierstrassCurve.deuringCurve_a₁ WeierstrassCurve.deuringVariableChange_u WeierstrassCurve.deuringCurve_a₃ WeierstrassCurve.deuringVariableChange_r ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine isUnit_Δ Affine.Y_eq_of_Y_ne mk.injEq a₃ a₁ map map_b₂ Ψ₃_ne_zero Ψ₃ mk a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq reduction toAffine Affine.Point natDegree_Ψ₃ map_a₁ Affine.equation_iff_nonsingular map_a₄ Affine.Point.some_ne_zero Δ VariableChange Affine.equation_iff preΨ'_three Affine.Point.neg_some map_a₂ j map_a₃ reduceHom Affine.Y_mem_of_X_mem Affine.nonsingular_residue reducePoint reducePoint_some_of_mem reducePoint_some_of_notMem Affine.vcX Affine.vcY Affine.vcXInv Affine.vcYInv Affine.vcX_vcXInv Affine.Point.vcFun Affine.Point.vcInvFun Affine.Point.vcFun_leftInverse Affine.Point.vcFun_rightInverse Affine.Point.equivOfVariableChangeEq Affine.Point.some_congr ratPointMap_zero ratPointMap_some ratPointMap_injective ratPointHom ratPointMap veluGx veluGy veluU veluT_eq veluQuotient veluX veluY Affine.Point.coordsOrZero Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one card_torsionBy_eq_sq_of_isAlgClosed exists_mul_Psi3_add_mul_derivative_Psi3 Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi Affine.Point.vcInvFun_add"
p2m_open "WeierstrassCurve"

namespace DeuringLevelThree

section ThreeTorsion

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in

theorem exists_equation_of_isAlgClosed [IsAlgClosed F] (x : F) :
    ∃ y : F, W.toAffine.Equation x y := by
  let b : F := W.a₁ * x + W.a₃
  let c : F := -(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  let q : F[X] := X ^ 2 + (C b * X + C c)
  have hlt : (C b * X + C c).degree < (X ^ 2 : F[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · exact lt_of_le_of_lt (degree_C_mul_X_le b) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hdeg : q.degree = 2 := by
    show (X ^ 2 + (C b * X + C c)).degree = 2
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
    rfl
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hdeg]; exact two_ne_zero)
  refine ⟨y, ?_⟩
  rw [Affine.equation_iff]
  have : y ^ 2 + (b * y + c) = 0 := by
    have := hy
    simp only [q, IsRoot.def, eval_add, eval_pow, eval_X, eval_mul, eval_C] at this
    exact this
  simp only [b, c] at this
  linear_combination this

variable {W}

theorem three_smul_eq_zero_of_eval_Ψ₃ [W.IsElliptic] {x y : F} (h : W.toAffine.Nonsingular x y)
    (hx : W.Ψ₃.eval x = 0) : (3 : ℤ) • (Affine.Point.some x y h) = 0 := by
  have h3 : (3 : ℕ) • Affine.Point.some x y h = 0 := by
    rw [Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W (by decide) h, preΨ'_three]
    exact hx
  exact_mod_cast h3

omit [DecidableEq F] in

theorem eval_derivative_Ψ₃_ne_zero [W.IsElliptic] (h3 : (3 : F) ≠ 0) {x : F}
    (hx : W.Ψ₃.eval x = 0) : W.Ψ₃.derivative.eval x ≠ 0 := by
  intro h0
  have key := congrArg (Polynomial.eval x) (W.exists_mul_Psi3_add_mul_derivative_Psi3)
  simp only [eval_add, eval_mul, hx, h0, mul_zero, zero_add, eval_C] at key
  have : (-3 : F) * W.Δ = 0 := key.symm
  rcases mul_eq_zero.mp this with e | e
  · exact h3 (neg_eq_zero.mp e)
  · exact W.isUnit_Δ.ne_zero e

omit [DecidableEq F] in
private theorem _root_.WeierstrassCurve.DeuringLevelThree.some_congr {x₁ y₁ x₂ y₂ : F} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

p2m_export "WeierstrassCurve.DeuringLevelThree" "some_congr"
variable (W) in

theorem exists_threeTorsion_basis [IsAlgClosed F] [W.IsElliptic] (h3 : (3 : F) ≠ 0) :
    ∃ (x₁ y₁ x₂ y₂ : F) (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂),
      (3 : ℤ) • Affine.Point.some x₁ y₁ h₁ = 0 ∧ (3 : ℤ) • Affine.Point.some x₂ y₂ h₂ = 0 ∧
      x₁ ≠ x₂ := by
  have hdeg : W.Ψ₃.natDegree = 4 := W.natDegree_Ψ₃ h3
  have hne0 : W.Ψ₃ ≠ 0 := W.Ψ₃_ne_zero h3
  have hdeg' : W.Ψ₃.degree = 4 := by rw [degree_eq_natDegree hne0, hdeg]; rfl
  obtain ⟨x₁, hx₁⟩ := IsAlgClosed.exists_root W.Ψ₃ (by rw [hdeg']; decide)
  rw [IsRoot.def] at hx₁

  set q := W.Ψ₃ /ₘ (X - C x₁) with hq
  have hfac : (X - C x₁) * q = W.Ψ₃ := (mul_divByMonic_eq_iff_isRoot).mpr hx₁
  have hqdeg : q.degree = 3 := by
    have := congrArg degree hfac
    rw [degree_mul, degree_X_sub_C, hdeg'] at this
    have hq0 : q ≠ 0 := fun h0 => by rw [h0, degree_zero] at this; exact absurd this (by decide)
    rw [degree_eq_natDegree hq0] at this ⊢
    have h13 : (1 + q.natDegree : WithBot ℕ) = (4 : ℕ) := by exact_mod_cast this
    have h13' : 1 + q.natDegree = 4 := by exact_mod_cast h13
    have : q.natDegree = 3 := by omega
    rw [this]; rfl
  obtain ⟨x₂, hx₂⟩ := IsAlgClosed.exists_root q (by rw [hqdeg]; decide)
  rw [IsRoot.def] at hx₂
  have hx₂' : W.Ψ₃.eval x₂ = 0 := by rw [← hfac, eval_mul, hx₂, mul_zero]
  have hne : x₁ ≠ x₂ := by
    intro h12
    subst h12
    apply eval_derivative_Ψ₃_ne_zero (W := W) h3 hx₁
    rw [← hfac, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
      eval_add, eval_mul, hx₂, eval_sub, eval_X, eval_C, sub_self, zero_mul, zero_add]
  obtain ⟨y₁, hy₁⟩ := exists_equation_of_isAlgClosed W x₁
  obtain ⟨y₂, hy₂⟩ := exists_equation_of_isAlgClosed W x₂
  have h₁ : W.toAffine.Nonsingular x₁ y₁ := (Affine.equation_iff_nonsingular).mp hy₁
  have h₂ : W.toAffine.Nonsingular x₂ y₂ := (Affine.equation_iff_nonsingular).mp hy₂
  exact ⟨x₁, y₁, x₂, y₂, h₁, h₂, three_smul_eq_zero_of_eval_Ψ₃ h₁ hx₁,
    three_smul_eq_zero_of_eval_Ψ₃ h₂ hx₂', hne⟩

end ThreeTorsion

section Torsion3

variable {G : Type*} [AddCommGroup G]

theorem zsmul_eq_emod_zsmul {T : G} (h3 : (3 : ℤ) • T = 0) (r : ℤ) : r • T = (r % 3) • T := by
  conv_lhs => rw [← Int.emod_add_mul_ediv r 3]
  rw [add_zsmul, mul_comm, mul_zsmul, h3, zsmul_zero, add_zero]

theorem zsmul_eq_zero_or_eq_or_eq_neg {T : G} (h3 : (3 : ℤ) • T = 0) (r : ℤ) :
    r • T = 0 ∨ r • T = T ∨ r • T = -T := by
  rw [zsmul_eq_emod_zsmul h3 r]
  have h0 : 0 ≤ r % 3 := Int.emod_nonneg _ (by norm_num)
  have h1 : r % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have h2T : (2 : ℤ) • T = -T := by
    rw [eq_neg_iff_add_eq_zero, ← add_one_zsmul]
    exact h3
  interval_cases (r % 3)
  · left; exact zero_zsmul _
  · right; left; exact one_zsmul _
  · right; right; exact h2T

theorem three_dvd_of_zsmul_eq_zero {T : G} (h3 : (3 : ℤ) • T = 0) (hT : T ≠ 0) {r : ℤ}
    (hr : r • T = 0) : (3 : ℤ) ∣ r := by
  by_contra hnd
  apply hT

  have hrr : r * r % 3 = 1 := by
    have h0 : 0 ≤ r % 3 := Int.emod_nonneg _ (by norm_num)
    have h1 : r % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have hne : r % 3 ≠ 0 := fun h => hnd (Int.dvd_of_emod_eq_zero h)
    rw [Int.mul_emod]
    interval_cases (r % 3)
    · exact absurd rfl hne
    · rfl
    · rfl
  calc T = (1 : ℤ) • T := (one_zsmul T).symm
    _ = (r * r % 3) • T := by rw [hrr]
    _ = (r * r) • T := (zsmul_eq_emod_zsmul h3 _).symm
    _ = r • r • T := mul_zsmul _ _ _
    _ = 0 := by rw [hr, zsmul_zero]

theorem three_dvd_and_three_dvd_of_zsmul_eq_zsmul {T₁ T₂ : G} (h₁ : (3 : ℤ) • T₁ = 0)
    (h₂ : (3 : ℤ) • T₂ = 0) (hT₁ : T₁ ≠ 0) (h20 : T₂ ≠ 0) (h21 : T₂ ≠ T₁) (h22 : T₂ ≠ -T₁)
    {c d : ℤ} (hcd : c • T₁ = d • T₂) : (3 : ℤ) ∣ c ∧ (3 : ℤ) ∣ d := by
  have hd : (3 : ℤ) ∣ d := by
    by_contra hnd
    have hdd : d * d % 3 = 1 := by
      have h0 : 0 ≤ d % 3 := Int.emod_nonneg _ (by norm_num)
      have h1 : d % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
      have hne : d % 3 ≠ 0 := fun h => hnd (Int.dvd_of_emod_eq_zero h)
      rw [Int.mul_emod]
      interval_cases (d % 3)
      · exact absurd rfl hne
      · rfl
      · rfl
    have hT₂ : T₂ = (d * c) • T₁ := by
      calc T₂ = (1 : ℤ) • T₂ := (one_zsmul T₂).symm
        _ = (d * d % 3) • T₂ := by rw [hdd]
        _ = (d * d) • T₂ := (zsmul_eq_emod_zsmul h₂ _).symm
        _ = d • d • T₂ := mul_zsmul _ _ _
        _ = d • c • T₁ := by rw [hcd]
        _ = (d * c) • T₁ := (mul_zsmul _ _ _).symm
    rcases zsmul_eq_zero_or_eq_or_eq_neg h₁ (d * c) with e | e | e
    · exact h20 (hT₂.trans e)
    · exact h21 (hT₂.trans e)
    · exact h22 (hT₂.trans e)
  refine ⟨?_, hd⟩
  have hd0 : d • T₂ = 0 := by
    obtain ⟨q, rfl⟩ := hd
    rw [mul_comm, mul_zsmul, h₂, zsmul_zero]
  exact three_dvd_of_zsmul_eq_zero h₁ hT₁ (hcd.trans hd0)

theorem exists_nsmul_add_nsmul_of_card_torsionBy
    (hcard : Nat.card (Submodule.torsionBy ℤ G (3 : ℤ)) = 9)
    {T₁ T₂ : G} (h₁ : (3 : ℤ) • T₁ = 0) (h₂ : (3 : ℤ) • T₂ = 0)
    (hT₁ : T₁ ≠ 0) (h20 : T₂ ≠ 0) (h21 : T₂ ≠ T₁) (h22 : T₂ ≠ -T₁)
    {U : G} (hU : (3 : ℤ) • U = 0) : ∃ a b : ℕ, U = a • T₁ + b • T₂ := by
  set M := Submodule.torsionBy ℤ G (3 : ℤ) with hM
  have hmem : ∀ {P : G}, (3 : ℤ) • P = 0 → P ∈ M := fun hP => (Submodule.mem_torsionBy_iff _ _).mpr hP
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype M := Fintype.ofFinite M
  have hcard' : Fintype.card M = 9 := by rw [← Nat.card_eq_fintype_card, hcard]

  have h3c : ∀ (c : ℤ) {T : G}, (3 : ℤ) • T = 0 → (3 : ℤ) • c • T = 0 := fun c T hT => by
    rw [← mul_zsmul, mul_comm, mul_zsmul, hT, zsmul_zero]
  let f : Fin 3 × Fin 3 → M := fun ab =>
    ⟨((ab.1 : ℕ) : ℤ) • T₁ + ((ab.2 : ℕ) : ℤ) • T₂,
      hmem (by rw [zsmul_add, h3c _ h₁, h3c _ h₂, add_zero])⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : ((a : ℕ) : ℤ) • T₁ + ((b : ℕ) : ℤ) • T₂ = ((a' : ℕ) : ℤ) • T₁ + ((b' : ℕ) : ℤ) • T₂ :=
      congrArg Subtype.val hab
    have hcd : (((a : ℕ) : ℤ) - a') • T₁ = (((b' : ℕ) : ℤ) - b) • T₂ := by
      rw [sub_zsmul, sub_zsmul, ← sub_eq_add_neg, ← sub_eq_add_neg, sub_eq_sub_iff_add_eq_add,
        hab', add_comm]
    obtain ⟨hc, hd⟩ := three_dvd_and_three_dvd_of_zsmul_eq_zsmul h₁ h₂ hT₁ h20 h21 h22 hcd
    have ha : (a : ℕ) = a' := by have := a.isLt; have := a'.isLt; omega
    have hb : (b : ℕ) = b' := by have := b.isLt; have := b'.isLt; omega
    rw [Prod.mk.injEq]
    exact ⟨Fin.ext ha, Fin.ext hb⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hcard', Fintype.card_prod, Fintype.card_fin]⟩
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨U, hmem hU⟩
  refine ⟨a, b, ?_⟩
  have := congrArg Subtype.val hab
  simp only [f] at this
  rw [← this, natCast_zsmul, natCast_zsmul]

end Torsion3

theorem veluX_map {F K : Type*} [Field F] [Field K] [DecidableEq K] (f : F →+* K)
    (W : WeierstrassCurve F) (S : Finset (F × F)) (x : F) :
    (W.map f).veluX (S.image (Prod.map f f)) (f x) = f (W.veluX S x) := by
  rw [veluX, veluX, Finset.sum_image ((f.injective.prodMap f.injective).injOn), map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [Prod.map_fst, Prod.map_snd, veluT_eq, veluU, veluGy, map_b₂, map_b₄, map_a₁, map_a₃,
    map_add, map_div₀, map_mul, map_pow, map_sub, map_neg, map_ofNat]

theorem veluY_map {F K : Type*} [Field F] [Field K] [DecidableEq K] (f : F →+* K)
    (W : WeierstrassCurve F) (S : Finset (F × F)) (x y : F) :
    (W.map f).veluY (S.image (Prod.map f f)) (f x) (f y) = f (W.veluY S x y) := by
  rw [veluY, veluY, Finset.sum_image ((f.injective.prodMap f.injective).injOn), map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [Prod.map_fst, Prod.map_snd, veluT_eq, veluU, veluGy, veluGx, map_b₂, map_b₄, map_a₁,
    map_a₂, map_a₃, map_a₄, map_add, map_div₀, map_mul, map_pow, map_sub, map_neg, map_ofNat]

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

theorem equivOfVariableChangeEq_one_some {X Y : WeierstrassCurve.Affine F}
    (h : (1 : VariableChange F) • X = Y) (x y : F) (hxy : Y.toAffine.Nonsingular x y) :
    ∃ hxy', Affine.Point.equivOfVariableChangeEq h (.some x y hxy) = .some x y hxy' := by
  obtain ⟨hxy', e⟩ := equivOfVariableChangeEq_some h x y hxy
  have hx : Affine.vcX (1 : VariableChange F) x = x := by
    show ((1 : Fˣ) : F) ^ 2 * x + 0 = x; simp
  have hy : Affine.vcY (1 : VariableChange F) x y = y := by
    show ((1 : Fˣ) : F) ^ 3 * y + ((1 : Fˣ) : F) ^ 2 * 0 * x + 0 = y; simp
  have hxy'' : X.toAffine.Nonsingular x y := by rw [hx, hy] at hxy'; exact hxy'
  exact ⟨hxy'', e.trans (some_congr hx hy _ _)⟩

theorem equivOfVariableChangeEq_one_symm_some {X Y : WeierstrassCurve.Affine F}
    (h : (1 : VariableChange F) • X = Y) (x y : F) (hxy : X.toAffine.Nonsingular x y) :
    ∃ hxy', (Affine.Point.equivOfVariableChangeEq h).symm (.some x y hxy) = .some x y hxy' := by
  obtain ⟨hxy', e⟩ := equivOfVariableChangeEq_symm_some h x y hxy
  have hx : Affine.vcXInv (1 : VariableChange F) x = x := by
    show (((1 : Fˣ)⁻¹ : Fˣ) : F) ^ 2 * (x - 0) = x; simp
  have hy : Affine.vcYInv (1 : VariableChange F) x y = y := by
    show (((1 : Fˣ)⁻¹ : Fˣ) : F) ^ 3 * (y - 0 - 0 * (x - 0)) = y; simp
  have hxy'' : Y.toAffine.Nonsingular x y := by rw [hx, hy] at hxy'; exact hxy'
  exact ⟨hxy'', e.trans (some_congr hx hy _ _)⟩

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

theorem eq_or_eq_neg_of_fst_eq' {x y y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x y') :
    Affine.Point.some x y' h' = Affine.Point.some x y h ∨
      Affine.Point.some x y' h' = -Affine.Point.some x y h := by
  by_cases hy : y' = W.toAffine.negY x y
  · right
    rw [Affine.Point.neg_some]
    exact Affine.Point.some_congr rfl hy _ _
  · left
    have := Affine.Y_eq_of_Y_ne h'.left h.left rfl hy
    subst this
    rfl

end RatPoint

open scoped Classical in
theorem main
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h2 : (2 : k) = 0)
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
        (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
          ∈ AddSubgroup.zmultiples Q₀ →
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x' y' h' : (E'.map B.subtype).toAffine.Point)
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

  have h3k : (3 : k) ≠ 0 := by
    rw [show (3 : k) = 2 + 1 by norm_num, h2, zero_add]; exact one_ne_zero

  obtain ⟨x₁, y₁, x₂, y₂, h₁, h₂, hP₁, hP₂, hx12⟩ := exists_threeTorsion_basis W h3k
  obtain ⟨B, φ, E', hE'ell, hΔ', hv', Q', hQ'ord, hRQ, γ, hγ, E₁', hΔ₁', h₁Ω, h₁red, e₁, t₁, e₂, t₂,
      hT₁, hT₂, e'₁, t'₁, e'₂, t'₂, hT'₁, hT'₂, h3T₁, h3T₂, hR₁, hR₂, hγ₁, hγ₂, hr₁, hs₁, hr₂, hs₂⟩ :=
    exists_valuationSubring_lift_variableChange_veluQuotient_apply_threeTorsion_eq_of_smul_eq_veluQuotient
      p h3k W n hm hsq Q₀ hQ₀ γ₀ hγ₀ h₁ h₂ hP₁ hP₂ hx12 Ω
  haveI := hE'ell
  refine ⟨B, φ, E', hE'ell, hΔ', 1, hv', Q', hQ'ord, hRQ, γ, hγ, ?_⟩
  intro x' y' h' x y h h3P hnot h3P' hred

  let S₀ := W.oddOrderSummingSet Q₀ n
  let Wq : WeierstrassCurve k := W.veluQuotient S₀
  let EΩ : WeierstrassCurve Ω := E'.map B.subtype
  let S' := EΩ.oddOrderSummingSet Q' n
  let Vq : WeierstrassCurve Ω := EΩ.veluQuotient S'
  let μ : W.toAffine.Point →+ (W.map φ.toRingHom).toAffine.Point := ratPointHom φ.toRingHom
  let ν : EΩ.toAffine.Point →+ (W.map φ.toRingHom).toAffine.Point :=
    (eqvSymmHom hv').comp (reduceHom hΔ')
  let μq : Wq.toAffine.Point →+ (Wq.map φ.toRingHom).toAffine.Point := ratPointHom φ.toRingHom
  let ν₁ : Vq.toAffine.Point →+ (Wq.map φ.toRingHom).toAffine.Point :=
    (eqvSymmHom h₁red).comp ((reduceHom hΔ₁').comp (eqvHom h₁Ω))
  have hν : ∀ P, ν P = (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' P) :=
    fun P => rfl
  have hν₁ : ∀ P, ν₁ P = (Affine.Point.equivOfVariableChangeEq h₁red).symm
      (reduceHom hΔ₁' (Affine.Point.equivOfVariableChangeEq h₁Ω P)) := fun P => rfl
  have hμinj : Function.Injective μ := fun a b hab => ratPointMap_injective φ.toRingHom hab
  have hμqinj : Function.Injective μq := fun a b hab => ratPointMap_injective φ.toRingHom hab
  have hEW : E'.map (residue B) = W.map φ.toRingHom := by rw [← hv', one_smul]
  have hmB : ((2 * n + 1 : ℕ) : ResidueField B) ≠ 0 := by
    rw [← map_natCast φ]; exact (map_ne_zero φ).mpr hm
  have hmΩ : ((2 * n + 1 : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  haveI : EΩ.IsElliptic := inferInstance
  have hVqell : Vq.IsElliptic := by
    show (EΩ.veluQuotient S').IsElliptic
    rw [← hγ]; infer_instance
  have hμsome : ∀ (a b : k) (hab : W.toAffine.Nonsingular a b),
      μ (.some a b hab) = .some (φ a) (φ b)
        (((W.toAffine.map_nonsingular φ.toRingHom.injective a b).mpr hab)) := fun a b hab => rfl
  have hμqsome : ∀ (a b : k) (hab : Wq.toAffine.Nonsingular a b),
      μq (.some a b hab) = .some (φ a) (φ b)
        (((Wq.toAffine.map_nonsingular φ.toRingHom.injective a b).mpr hab)) := fun a b hab => rfl

  have hRED : ∀ (f t : B) (hT : EΩ.toAffine.Nonsingular f t),
      ∃ hh, ν (.some (f : Ω) t hT) = .some (residue B f) (residue B t) hh := by
    intro f t hT
    have hfmem : (f : Ω) ∈ B := f.2
    have hred1 : reduceHom hΔ' (.some (f : Ω) t hT) = reducePoint hΔ' (.some (f : Ω) t hT) := rfl
    rw [hν, hred1, reducePoint_some_of_mem hΔ' hT hfmem]
    obtain ⟨hxy', e⟩ := equivOfVariableChangeEq_one_symm_some hv'
      (residue B ⟨(f : Ω), hfmem⟩) (residue B ⟨t, Affine.Y_mem_of_X_mem E' hT.1 hfmem⟩)
      (Affine.nonsingular_residue E' hΔ' hT.1)
    rw [e]
    have hff : (⟨(f : Ω), hfmem⟩ : B) = f := Subtype.ext rfl
    have htt : (⟨(t : Ω), Affine.Y_mem_of_X_mem E' hT.1 hfmem⟩ : B) = t := Subtype.ext rfl
    have hh : (W.map φ.toRingHom).toAffine.Nonsingular (residue B f) (residue B t) := by
      have := hxy'; rw [hff, htt] at this; exact this
    refine ⟨hh, some_congr (by rw [hff]) (by rw [htt]) _ _⟩

  have hRED₁ : ∀ (X Y : Ω) (hX : X ∈ B) (hY : Y ∈ B) (hU : Vq.toAffine.Nonsingular X Y),
      ∃ hh, ν₁ (.some X Y hU) = .some (residue B ⟨X, hX⟩) (residue B ⟨Y, hY⟩) hh := by
    intro X Y hX hY hU
    rw [hν₁]
    obtain ⟨hU', e1⟩ := equivOfVariableChangeEq_one_some h₁Ω X Y hU
    rw [e1]
    have hred1 : reduceHom hΔ₁' (.some X Y hU') = reducePoint hΔ₁' (.some X Y hU') := rfl
    rw [hred1, reducePoint_some_of_mem hΔ₁' hU' hX]
    obtain ⟨hxy', e⟩ := equivOfVariableChangeEq_one_symm_some h₁red
      (residue B ⟨X, hX⟩) (residue B ⟨Y, Affine.Y_mem_of_X_mem E₁' hU'.1 hX⟩)
      (Affine.nonsingular_residue E₁' hΔ₁' hU'.1)
    rw [e]
    exact ⟨_, rfl⟩

  have hx'mem : x' ∈ B := by
    by_contra hx'
    have h0 : ν (.some x' y' h') = 0 := by
      rw [hν, show reduceHom hΔ' (.some x' y' h') = reducePoint hΔ' (.some x' y' h') from rfl,
        reducePoint_some_of_notMem hΔ' h' hx', ← eqvSymmHom_apply, map_zero]
    have := hred
    change μ (Affine.Point.some x y h) = ν (Affine.Point.some x' y' h') at this
    rw [h0, hμsome] at this
    exact Affine.Point.some_ne_zero _ this
  have hy'mem : y' ∈ B := Affine.Y_mem_of_X_mem E' h'.1 hx'mem
  have hres_x : residue B ⟨x', hx'mem⟩ = φ x ∧ residue B ⟨y', hy'mem⟩ = φ y := by
    obtain ⟨hh, e⟩ := hRED ⟨x', hx'mem⟩ ⟨y', hy'mem⟩ h'
    have := hred
    change μ (Affine.Point.some x y h) = ν (Affine.Point.some x' y' h') at this
    rw [e, hμsome, Affine.Point.some.injEq] at this
    exact ⟨this.1.symm, this.2.symm⟩

  obtain ⟨πk, hπk_ker, hπk⟩ :=
    exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one W n hm Q₀ hQ₀
  obtain ⟨πΩ, hπΩ_ker, hπΩ⟩ :=
    exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one EΩ n hmΩ Q' hQ'ord
  have hμQ : addOrderOf (μ Q₀) = 2 * n + 1 := (addOrderOf_injective μ hμinj Q₀).trans hQ₀
  have hνQ : ν Q' = μ Q₀ := by rw [hν]; exact hRQ.symm
  have hpre : ∀ P : W.toAffine.Point, μ P ∈ AddSubgroup.zmultiples (μ Q₀) →
      P ∈ AddSubgroup.zmultiples Q₀ := by
    intro P hP
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
    rw [← map_zsmul] at hj
    rw [← hμinj hj]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _
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

  obtain ⟨h₀'', hπkP⟩ := hπk x y h hnot
  obtain ⟨h'', hπΩP⟩ := hπΩ x' y' h' hP'not
  refine ⟨h'', h₀'', ?_⟩
  have h3U' : (3 : ℤ) • (Affine.Point.some _ _ h'' : Vq.toAffine.Point) = 0 := by
    rw [← hπΩP, ← map_zsmul, ← AddMonoidHom.mem_ker, hπΩ_ker]; exact h3P'

  have hredQ' : reduceHom hΔ' Q' = Affine.Point.equivOfVariableChangeEq hv' (μ Q₀) := by
    rw [← Equiv.symm_apply_eq]; exact hRQ.symm
  have hordQ' : addOrderOf (reduceHom hΔ' Q') = 2 * n + 1 := by
    rw [hredQ', addOrderOf_equivOfVariableChangeEq, hμQ]
  have hSbar : (E'.map (residue B)).oddOrderSummingSet (reduceHom hΔ' Q') n =
      S₀.image (Prod.map φ.toRingHom φ.toRingHom) := by
    rw [hredQ', oddOrderSummingSet_equivOfVariableChangeEq_one, oddOrderSummingSet_ratPointHom]
  have hx'S : ∀ P ∈ (E'.map (residue B)).oddOrderSummingSet (reduceHom hΔ' Q') n,
      P.1 ≠ residue B ⟨x', hx'mem⟩ := by
    intro P hP hP1
    rw [hSbar, Finset.mem_image] at hP
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hP
    rw [hres_x.1] at hP1
    have hax : a = x := φ.injective hP1
    subst hax

    rw [mem_oddOrderSummingSet] at hab
    obtain ⟨j, hj1, hjn, hjQ⟩ := hab
    have hj0 : j • Q₀ ≠ 0 := nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ₀]; omega)
    apply hnot
    rcases hjQ' : j • Q₀ with _ | ⟨a', b', hab'⟩
    · exact absurd hjQ' hj0
    · rw [hjQ', Affine.Point.coordsOrZero_some, Prod.mk.injEq] at hjQ
      obtain ⟨rfl, rfl⟩ := hjQ
      have hjmem : (Affine.Point.some a' b' hab' : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q₀ := by
        rw [← hjQ']; exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _
      rcases eq_or_eq_neg_of_fst_eq' hab' h with e | e
      · rw [e]; exact hjmem
      · rw [e]; exact AddSubgroup.neg_mem _ hjmem
  obtain ⟨hXmem, hGX⟩ :=
    veluX_mem_and_residue_veluX_eq_of_forall_fst_ne_residue hΔ' hmB Q' hQ'ord hordQ' hx'mem hx'S
  obtain ⟨hYmem, hGY⟩ :=
    veluY_mem_and_residue_veluY_eq_of_forall_fst_ne_residue hΔ' hmB Q' hQ'ord hordQ' hx'mem hy'mem
      hx'S
  have hGX' : residue B ⟨EΩ.veluX S' x', hXmem⟩ = φ (W.veluX S₀ x) := by
    rw [hGX, hSbar, hres_x.1, hEW]
    exact veluX_map φ.toRingHom W S₀ x
  have hGY' : residue B ⟨EΩ.veluY S' x' y', hYmem⟩ = φ (W.veluY S₀ x y) := by
    rw [hGY, hSbar, hres_x.1, hres_x.2, hEW]
    exact veluY_map φ.toRingHom W S₀ x y
  have hUU : μq (Affine.Point.some _ _ h₀'') = ν₁ (Affine.Point.some _ _ h'') := by
    obtain ⟨hh, e⟩ := hRED₁ _ _ hXmem hYmem h''
    rw [e, hμqsome]
    exact some_congr hGX'.symm hGY'.symm _ _

  have hγinj : Function.Injective (Affine.Point.equivOfVariableChangeEq hγ) :=
    (Affine.Point.equivOfVariableChangeEq hγ).injective
  have h3γ : ∀ P : Vq.toAffine.Point, (3 : ℤ) • Affine.Point.equivOfVariableChangeEq hγ P =
      Affine.Point.equivOfVariableChangeEq hγ ((3 : ℤ) • P) := fun P => by
    rw [← eqvHom_apply, ← eqvHom_apply, map_zsmul]
  have h3T'₁ : (3 : ℤ) • (Affine.Point.some _ _ hT'₁ : Vq.toAffine.Point) = 0 := by
    apply hγinj
    rw [← h3γ, hγ₁, h3T₁, ← eqvHom_apply, map_zero]
  have h3T'₂ : (3 : ℤ) • (Affine.Point.some _ _ hT'₂ : Vq.toAffine.Point) = 0 := by
    apply hγinj
    rw [← h3γ, hγ₂, h3T₂, ← eqvHom_apply, map_zero]
  have hvcinj : Function.Injective (Affine.vcXInv γ₀) := fun a b hab => by
    rw [← Affine.vcX_vcXInv (C := γ₀) a, ← Affine.vcX_vcXInv (C := γ₀) b]; exact congrArg _ hab
  have he'12 : (e'₁ : Ω) ≠ e'₂ := by
    intro h12
    apply hx12
    apply hvcinj
    have := congrArg (residue B) (Subtype.ext h12 : e'₁ = e'₂)
    rw [hr₁, hr₂] at this
    exact φ.injective this
  have hT'20 : (Affine.Point.some _ _ hT'₂ : Vq.toAffine.Point) ≠ 0 := Affine.Point.some_ne_zero _
  have hT'21 : (Affine.Point.some _ _ hT'₂ : Vq.toAffine.Point) ≠ Affine.Point.some _ _ hT'₁ := by
    intro h21
    exact he'12 ((Affine.Point.some.injEq _ _ _ _ _ _).mp h21).1.symm
  have hT'22 : (Affine.Point.some _ _ hT'₂ : Vq.toAffine.Point) ≠ -Affine.Point.some _ _ hT'₁ := by
    intro h22
    rw [Affine.Point.neg_some] at h22
    exact he'12 ((Affine.Point.some.injEq _ _ _ _ _ _).mp h22).1.symm
  have hcard : Nat.card (Submodule.torsionBy ℤ Vq.toAffine.Point (3 : ℤ)) = 9 := by
    have h := @card_torsionBy_eq_sq_of_isAlgClosed Ω _ _ _ Vq hVqell 3 (by norm_num) two_ne_zero
    simpa using h
  obtain ⟨a, b, hab⟩ := exists_nsmul_add_nsmul_of_card_torsionBy hcard h3T'₁ h3T'₂
    (Affine.Point.some_ne_zero _) hT'20 hT'21 hT'22 h3U'

  obtain ⟨h₁', hP'₁⟩ := equivOfVariableChangeEq_symm_some hγ₀ x₁ y₁ h₁
  obtain ⟨h₂', hP'₂⟩ := equivOfVariableChangeEq_symm_some hγ₀ x₂ y₂ h₂
  have hν₁T'₁ : ν₁ (.some _ _ hT'₁) = μq (.some _ _ h₁') := by
    obtain ⟨hh, e⟩ := hRED₁ (e'₁ : Ω) (t'₁ : Ω) e'₁.2 t'₁.2 hT'₁
    rw [e, hμqsome]
    refine some_congr ?_ ?_ _ _
    · rw [← hr₁]
    · rw [← hs₁]
  have hν₁T'₂ : ν₁ (.some _ _ hT'₂) = μq (.some _ _ h₂') := by
    obtain ⟨hh, e⟩ := hRED₁ (e'₂ : Ω) (t'₂ : Ω) e'₂.2 t'₂.2 hT'₂
    rw [e, hμqsome]
    refine some_congr ?_ ?_ _ _
    · rw [← hr₂]
    · rw [← hs₂]

  have hUb : (Affine.Point.some _ _ h₀'' : Wq.toAffine.Point) =
      a • Affine.Point.some _ _ h₁' + b • Affine.Point.some _ _ h₂' := by
    apply hμqinj
    rw [hUU, hab, map_add, map_nsmul, map_nsmul, hν₁T'₁, hν₁T'₂, map_add, map_nsmul, map_nsmul]

  have hνT₁ : μ (.some x₁ y₁ h₁) = ν (.some _ _ hT₁) := hR₁
  have hνT₂ : μ (.some x₂ y₂ h₂) = ν (.some _ _ hT₂) := hR₂

  have hL : Affine.Point.equivOfVariableChangeEq hγ₀ (Affine.Point.some _ _ h₀'') =
      a • Affine.Point.some x₁ y₁ h₁ + b • Affine.Point.some x₂ y₂ h₂ := by
    rw [hUb, ← eqvHom_apply, map_add, map_nsmul, map_nsmul, eqvHom_apply, eqvHom_apply, ← hP'₁,
      ← hP'₂, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

  have hR : Affine.Point.equivOfVariableChangeEq hγ (Affine.Point.some _ _ h'') =
      a • Affine.Point.some _ _ hT₁ + b • Affine.Point.some _ _ hT₂ := by
    rw [hab, ← eqvHom_apply, map_add, map_nsmul, map_nsmul, eqvHom_apply, eqvHom_apply, hγ₁, hγ₂]
  show μ (Affine.Point.equivOfVariableChangeEq hγ₀ (Affine.Point.some _ _ h₀'')) =
    ν (Affine.Point.equivOfVariableChangeEq hγ (Affine.Point.some _ _ h''))
  rw [hL, hR, map_add, map_nsmul, map_nsmul, map_add, map_nsmul, map_nsmul, hνT₁, hνT₂]

end DeuringLevelThree

end WeierstrassCurve

open scoped Classical in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (h2 : (2 : k) = 0)
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
        (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
          ∈ AddSubgroup.zmultiples Q₀ →
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x' y' h' : (E'.map B.subtype).toAffine.Point)
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
  WeierstrassCurve.DeuringLevelThree.main p h2 W n hm hsq Q₀ hQ₀ γ₀ hγ₀ Ω

end S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero (solution)
