-- Prove2me | solution 1 for WeierstrassCurve.fullKernelHom_eq_veluPointMap2_comp_of_stage_last
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b3b12d0f-5923-5492-8d6d-a0d7124de23f

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_fullKernelHom_eq_veluPointMap2_comp_of_stage_last
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"

set_option autoImplicit false

p2m_open "WeierstrassCurve~veluY~veluX P2MW.S_WeierstrassCurve_fullKernelHom_eq_veluPointMap2_comp_of_stage_last.WeierstrassCurve WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine VariableChange.one_def Affine.negY a₃ a₁ map a₄ a₂ a₆ Affine.Point.some Affine.negAddY toAffine Affine.Point Affine.addX ψ₂ Δ VariableChange Affine.addY Affine.Y_eq_of_X_eq Affine.equation_iff j fullKernelQuotient fullKernelQuotient_two veluGx veluGy veluT veluU veluQuotient2 velu2X velu2Y veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne exists_addMonoidHom_coe_eq_veluPointMap2 fullKernelQuotient_discriminant_ne_zero fullKernelHom_surjective_of_isAlgClosed"
p2m_open "WeierstrassCurve~veluY~veluX"

section Transport

variable {K : Type*} [Field K] [DecidableEq K]

private theorem equivOfVariableChangeEq_symm_add (C : VariableChange K) (W : WeierstrassCurve.Affine K)
    {V : WeierstrassCurve.Affine K} (h : C • W = V) (P Q : W.Point) :
    (Point.equivOfVariableChangeEq h).symm (P + Q) =
      (Point.equivOfVariableChangeEq h).symm P + (Point.equivOfVariableChangeEq h).symm Q := by
  subst h
  exact Point.vcInvFun_add C W P Q

private noncomputable def transportAddEquiv (C : VariableChange K) (W : WeierstrassCurve.Affine K)
    {V : WeierstrassCurve.Affine K} (h : C • W = V) : W.Point ≃+ V.Point :=
  AddEquiv.mk' (Point.equivOfVariableChangeEq h).symm (equivOfVariableChangeEq_symm_add C W h)

@[scoped simp] private theorem transportAddEquiv_apply (C : VariableChange K) (W : WeierstrassCurve.Affine K)
    {V : WeierstrassCurve.Affine K} (h : C • W = V) (P : W.Point) :
    transportAddEquiv C W h P = (Point.equivOfVariableChangeEq h).symm P := rfl

end Transport

section Cleared

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

private theorem _root_.WeierstrassCurve.velu_pair_x_cleared {x y x₀ y₀ : R}
    (hP : W.toAffine.Equation x y) (hR : W.toAffine.Equation x₀ y₀) :
    ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
      + ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
          - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
      = W.veluT x₀ y₀ * (x - x₀) + W.veluU x₀ y₀ := by
  rw [Affine.equation_iff] at hP hR
  simp only [veluT, veluU, veluGx, veluGy]
  linear_combination 2 * hP - 2 * hR

p2m_export "WeierstrassCurve" "velu_pair_x_cleared"

private theorem _root_.WeierstrassCurve.velu_pair_y_cleared {x y x₀ y₀ : R}
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

p2m_export "WeierstrassCurve" "velu_pair_y_cleared"
end Cleared

section PairField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private theorem _root_.WeierstrassCurve.addX_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addX x x₀ ((y - y₀) / (x - x₀)) - x₀
      = ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
          / (x - x₀) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  simp only [Affine.addX]
  field_simp
  ring1

p2m_export "WeierstrassCurve" "addX_sub_eq_div"
private theorem _root_.WeierstrassCurve.addX_neg_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addX x x₀ ((y - W.toAffine.negY x₀ y₀) / (x - x₀)) - x₀
      = ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
          - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2) / (x - x₀) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  simp only [Affine.addX, Affine.negY]
  field_simp
  ring1

p2m_export "WeierstrassCurve" "addX_neg_sub_eq_div"
private theorem _root_.WeierstrassCurve.addY_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addY x x₀ y ((y - y₀) / (x - x₀)) - y₀
      = ((-((y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) - y₀ * (x - x₀) ^ 3) / (x - x₀) ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 hd)]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  ring1

p2m_export "WeierstrassCurve" "addY_sub_eq_div"
private theorem _root_.WeierstrassCurve.addY_neg_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
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

p2m_export "WeierstrassCurve" "addY_neg_sub_eq_div"
variable [DecidableEq F]

private theorem _root_.WeierstrassCurve.velu_pair {x y x₀ y₀ : F}
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
  · rw [W.addX_sub_eq_div hd, W.addX_neg_sub_eq_div hd, ← add_div, W.velu_pair_x_cleared hP hR,
      div_add_div _ _ hd (pow_ne_zero 2 hd), div_eq_div_iff (pow_ne_zero 2 hd) (mul_ne_zero hd (pow_ne_zero 2 hd))]
    ring
  · rw [W.addY_sub_eq_div hd, W.addY_neg_sub_eq_div hd, ← add_div, W.velu_pair_y_cleared hP hR, neg_div,
      neg_inj, div_add_div _ _ (pow_ne_zero 3 hd) (pow_ne_zero 2 hd), div_add_div _ _
        (mul_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hd)) (pow_ne_zero 2 hd),
      div_eq_div_iff (pow_ne_zero 3 hd)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hd)) (pow_ne_zero 2 hd))]
    ring

p2m_export "WeierstrassCurve" "velu_pair"
end PairField

private theorem _root_.WeierstrassCurve.some_eq_of_X_eq_of_veluGy_eq_zero' {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x₀ y₀ y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (h : W.toAffine.Nonsingular x₀ y) :
    (Affine.Point.some x₀ y h : W.toAffine.Point) = Affine.Point.some x₀ y₀ h₀ := by
  have hneg : W.toAffine.negY x₀ y₀ = y₀ := by
    simp only [veluGy] at hgy
    simp only [Affine.negY]
    linear_combination hgy
  have hy : y = y₀ := by
    rcases Affine.Y_eq_of_X_eq h.1 h₀.1 rfl with hy | hy
    · exact hy
    · rw [hy, hneg]
  subst hy
  rfl

p2m_export "WeierstrassCurve" "some_eq_of_X_eq_of_veluGy_eq_zero'"

private theorem _root_.WeierstrassCurve.velu2_translate {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (h2 : (2 : F) ≠ 0) {x y x₀ y₀ : F} (h : W.toAffine.Nonsingular x y) (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.velu2X x₀ y₀ x = x + ((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.1 - x₀) ∧
    W.velu2Y x₀ y₀ x y = y + ((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.2 - y₀) := by
  have hnegT : -(Point.some x₀ y₀ h₀ : W.toAffine.Point) = Point.some x₀ y₀ h₀ := by
    rw [Point.neg_some]
    exact W.some_eq_of_X_eq_of_veluGy_eq_zero' h₀ hgy _
  have hp := W.velu_pair h h₀ hx
  rw [hnegT] at hp
  simp only [Point.coordsOrZero_some] at hp
  have hU : W.veluU x₀ y₀ = 0 := by rw [veluU, hgy]; ring
  have hTt : W.veluT x₀ y₀ = 2 * W.veluGx x₀ y₀ := by rw [veluT, hgy]; ring
  rw [hU, hTt, hgy] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have key1 : 2 * ((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.1 - x₀)
      = 2 * (W.veluGx x₀ y₀ / (x - x₀)) := by
    rw [two_mul, hp1]; ring
  have key2 : 2 * ((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.2 - y₀)
      = 2 * (-(W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2)) := by
    rw [two_mul, hp2]; ring
  refine ⟨?_, ?_⟩
  · rw [mul_left_cancel₀ h2 key1, velu2X]
  · rw [mul_left_cancel₀ h2 key2, velu2Y]; ring

p2m_export "WeierstrassCurve" "velu2_translate"

private theorem eq_zero_or_eq_of_veluPointMap2_eq_zero {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    (h2 : (2 : F) ≠ 0) {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) (R : W.toAffine.Point)
    (hR : veluPointMap2 h2 h₀.1 hgy hΔ R = 0) :
    R = 0 ∨ R = Point.some x₀ y₀ h₀ := by
  rcases R with _ | ⟨x, y, h⟩
  · exact Or.inl rfl
  · right
    by_cases hx : x = x₀
    · subst hx
      exact W.some_eq_of_X_eq_of_veluGy_eq_zero' h₀ hgy h
    · rw [veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ h hx] at hR
      exact absurd hR (Point.some_ne_zero _)

private theorem _root_.WeierstrassCurve.exists_two_torsion_data
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] {m : ℕ}
    (hN : ((2 * (m + 1) : ℕ) : F) ≠ 0) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1)) :
    (2 : F) ≠ 0 ∧ ((m + 1 : ℕ) : F) ≠ 0 ∧
    ∃ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      (m + 1) • Q = Point.some x₀ y₀ h₀ ∧ W.veluGy x₀ y₀ = 0 ∧ (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by
  have hN' : (2 : F) * ((m : F) + 1) ≠ 0 := by push_cast at hN; exact hN
  have h2 : (2 : F) ≠ 0 := (mul_ne_zero_iff.mp hN').1
  have hm1 : ((m + 1 : ℕ) : F) ≠ 0 := by push_cast; exact (mul_ne_zero_iff.mp hN').2
  have hT0 : (m + 1) • Q ≠ 0 := _root_.nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
  have h2T : 2 • ((m + 1) • Q) = 0 := by rw [← mul_nsmul', ← hQ, addOrderOf_nsmul_eq_zero]
  obtain ⟨x₀, y₀, h₀, hT⟩ :
      ∃ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀), (m + 1) • Q = Point.some x₀ y₀ h₀ := by
    rcases hmq : (m + 1) • Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hmq hT0
    · exact ⟨x₀, y₀, h₀, rfl⟩
  have hgy : W.veluGy x₀ y₀ = 0 := by
    have hneg : -((m + 1) • Q) = (m + 1) • Q := by
      rw [neg_eq_iff_add_eq_zero, ← two_nsmul, h2T]
    rw [hT, Point.neg_some, Point.some.injEq] at hneg
    have hy := hneg.2
    simp only [veluGy, Affine.negY] at hy ⊢
    linear_combination hy
  have hΔ₂ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0 := by
    have hT2 : addOrderOf ((m + 1) • Q) = 2 := addOrderOf_eq_prime h2T hT0
    have h2n : ((2 : ℕ) : F) ≠ 0 := by exact_mod_cast h2
    have hD := fullKernelQuotient_discriminant_ne_zero 2 W h2n ((m + 1) • Q) hT2
    rwa [hT, fullKernelQuotient_two W h₀ hgy] at hD
  exact ⟨h2, hm1, x₀, y₀, h₀, hT, hgy, hΔ₂⟩

p2m_export "WeierstrassCurve" "exists_two_torsion_data"

section NatpFurniture

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
private lemma some_ext {W' : Affine K} {x₁ x₂ y₁ y₂ : K} {h₁ : W'.Nonsingular x₁ y₁}
    {h₂ : W'.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

omit [DecidableEq K] in

private theorem point_eq_of_ne_zero_of_coordsOrZero_eq {W' : Affine K} {X Y : W'.Point}
    (hX : X ≠ 0) (hY : Y ≠ 0) (h : X.coordsOrZero = Y.coordsOrZero) : X = Y := by
  rcases X with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hX
  rcases Y with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hY
  exact some_ext (congrArg Prod.fst h) (congrArg Prod.snd h)

end NatpFurniture

private theorem addMonoidHom_eq_of_ker_eq_of_coordsOrZero_eq {K : Type*} [Field K] [DecidableEq K]
    {W' V' : Affine K} (Q : W'.Point) (ψ₁ ψ₂ : W'.Point →+ V'.Point)
    (h₁ : ψ₁.ker = AddSubgroup.zmultiples Q) (h₂ : ψ₂.ker = AddSubgroup.zmultiples Q)
    (h : ∀ P : W'.Point, P ∉ AddSubgroup.zmultiples Q →
      (ψ₁ P).coordsOrZero = (ψ₂ P).coordsOrZero) :
    ψ₁ = ψ₂ := by
  ext P
  by_cases hP : P ∈ AddSubgroup.zmultiples Q
  · have m₁ : P ∈ ψ₁.ker := by rw [h₁]; exact hP
    have m₂ : P ∈ ψ₂.ker := by rw [h₂]; exact hP
    simp only [AddMonoidHom.mem_ker] at m₁ m₂
    rw [m₁, m₂]
  · refine point_eq_of_ne_zero_of_coordsOrZero_eq ?_ ?_ (h P hP)
    · intro h0
      exact hP (by rw [← h₁]; exact AddMonoidHom.mem_ker.mpr h0)
    · intro h0
      exact hP (by rw [← h₂]; exact AddMonoidHom.mem_ker.mpr h0)

private theorem sum_Icc_parity_split {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1), g k
      = g 1 + ∑ j ∈ Finset.Icc 1 m, (g (2 * j) + g (2 * j + 1)) := by
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty_of_lt (Nat.lt_succ_self 0), Finset.sum_empty, add_zero]
    show ∑ k ∈ Finset.Icc 1 1, g k = g 1
    rw [Finset.Icc_self, Finset.sum_singleton]
  | succ n ih =>
    have e0 : 2 * (n + 1 + 1) - 1 = 2 * (n + 1) - 1 + 1 + 1 := by omega
    have e1 : 2 * (n + 1) - 1 + 1 = 2 * (n + 1) := by omega
    rw [e0, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih,
      Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega), e1, add_assoc, add_assoc]

private theorem not_mem_zmultiples_two_nsmul {A : Type*} [AddGroup A] {m : ℕ} (Q : A)
    (hQ : addOrderOf Q = 2 * (m + 1)) : Q ∉ AddSubgroup.zmultiples (2 • Q) := by
  intro h
  have h1 : addOrderOf Q ∣ addOrderOf (2 • Q) := addOrderOf_dvd_of_mem_zmultiples h
  have h2 : addOrderOf (2 • Q) ∣ m + 1 := by
    refine addOrderOf_dvd_of_nsmul_eq_zero ?_
    rw [← mul_nsmul, ← hQ, addOrderOf_nsmul_eq_zero]
  have h3 := Nat.le_of_dvd (Nat.succ_pos m) (h1.trans h2)
  omega

private theorem _root_.WeierstrassCurve.coordsOrZero_veluPointMap2_fullKernelHom
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {m : ℕ}
    (h2 : (2 : F) ≠ 0) (Q : W.toAffine.Point)
    (ρ : W.toAffine.Point →+ (W.fullKernelQuotient (2 • Q) (m + 1)).toAffine.Point)
    (hρker : ρ.ker = AddSubgroup.zmultiples (2 • Q))
    {x₁ y₁ : F} (h₁ : (W.fullKernelQuotient (2 • Q) (m + 1)).toAffine.Nonsingular x₁ y₁)
    (hT₁ : ρ Q = Point.some x₁ y₁ h₁)
    (hgy₁ : (W.fullKernelQuotient (2 • Q) (m + 1)).veluGy x₁ y₁ = 0)
    (hΔ₁ : ((W.fullKernelQuotient (2 • Q) (m + 1)).veluQuotient2 x₁ y₁).Δ ≠ 0) :
    ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (veluPointMap2 h2 h₁.1 hgy₁ hΔ₁ (ρ P)).coordsOrZero =
        ((ρ P).coordsOrZero.1 + ((ρ (P + Q)).coordsOrZero.1 - (ρ Q).coordsOrZero.1),
         (ρ P).coordsOrZero.2 + ((ρ (P + Q)).coordsOrZero.2 - (ρ Q).coordsOrZero.2)) := by
  intro P hP

  have hle : AddSubgroup.zmultiples (2 • Q) ≤ AddSubgroup.zmultiples Q :=
    AddSubgroup.zmultiples_le_of_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) 2)
  have hP0 : ρ P ≠ 0 := fun h0 =>
    hP (hle (by rw [← hρker]; exact AddMonoidHom.mem_ker.mpr h0))
  have hPT : ρ P ≠ ρ Q := fun heq =>
    hP (by
      have hk : P - Q ∈ AddSubgroup.zmultiples (2 • Q) := by
        rw [← hρker, AddMonoidHom.mem_ker, map_sub, heq, sub_self]
      have hPm := AddSubgroup.add_mem _ (hle hk) (AddSubgroup.mem_zmultiples Q)
      rwa [sub_add_cancel] at hPm)
  rw [map_add]
  rcases hRP : ρ P with _ | ⟨x, y, h⟩
  · exact absurd hRP hP0
  · have hx : x ≠ x₁ := by
      intro hx
      apply hPT
      rw [hRP, hT₁]
      subst hx
      exact (W.fullKernelQuotient (2 • Q) (m + 1)).some_eq_of_X_eq_of_veluGy_eq_zero' h₁ hgy₁ h
    rw [veluPointMap2_some_of_ne h2 h₁.1 hgy₁ hΔ₁ h hx, hT₁]
    obtain ⟨e1, e2⟩ := (W.fullKernelQuotient (2 • Q) (m + 1)).velu2_translate h2 h h₁ hgy₁ hx
    simp only [Point.coordsOrZero_some]
    rw [e1, e2]

p2m_export "WeierstrassCurve" "coordsOrZero_veluPointMap2_fullKernelHom"

private theorem _root_.WeierstrassCurve.veluPointMap2_comp_fullKernelHom_pinned
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {m : ℕ}
    (h2 : (2 : F) ≠ 0) (Q : W.toAffine.Point)
    (ρ : W.toAffine.Point →+ (W.fullKernelQuotient (2 • Q) (m + 1)).toAffine.Point)
    (hρker : ρ.ker = AddSubgroup.zmultiples (2 • Q))
    (hρ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples (2 • Q) →
      (ρ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (m + 1 - 1),
            ((P + k • (2 • Q)).coordsOrZero.1 - (k • (2 • Q)).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (m + 1 - 1),
            ((P + k • (2 • Q)).coordsOrZero.2 - (k • (2 • Q)).coordsOrZero.2)))
    {x₁ y₁ : F} (h₁ : (W.fullKernelQuotient (2 • Q) (m + 1)).toAffine.Nonsingular x₁ y₁)
    (hT₁ : ρ Q = Point.some x₁ y₁ h₁)
    (hgy₁ : (W.fullKernelQuotient (2 • Q) (m + 1)).veluGy x₁ y₁ = 0)
    (hΔ₁ : ((W.fullKernelQuotient (2 • Q) (m + 1)).veluQuotient2 x₁ y₁).Δ ≠ 0) :
    ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (veluPointMap2 h2 h₁.1 hgy₁ hΔ₁ (ρ P)).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) := by
  intro P hP
  have hle : AddSubgroup.zmultiples (2 • Q) ≤ AddSubgroup.zmultiples Q :=
    AddSubgroup.zmultiples_le_of_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) 2)
  have hP2 : P ∉ AddSubgroup.zmultiples (2 • Q) := fun h => hP (hle h)
  have hPQ2 : P + Q ∉ AddSubgroup.zmultiples (2 • Q) := fun h =>
    hP (by
      have hPm := AddSubgroup.sub_mem _ (hle h) (AddSubgroup.mem_zmultiples Q)
      rwa [add_sub_cancel_right] at hPm)

  have hQ2 : Q ∉ AddSubgroup.zmultiples (2 • Q) := fun h => by
    rw [← hρker, AddMonoidHom.mem_ker, hT₁] at h
    exact Point.some_ne_zero h₁ h

  have hsummand : ∀ j ∈ Finset.Icc 1 m,
      (((P + (2 * j) • Q).coordsOrZero.1 - ((2 * j) • Q).coordsOrZero.1)
          + ((P + (2 * j + 1) • Q).coordsOrZero.1 - ((2 * j + 1) • Q).coordsOrZero.1)
        = ((P + j • (2 • Q)).coordsOrZero.1 - (j • (2 • Q)).coordsOrZero.1)
          + (((P + Q + j • (2 • Q)).coordsOrZero.1 - (j • (2 • Q)).coordsOrZero.1)
            - ((Q + j • (2 • Q)).coordsOrZero.1 - (j • (2 • Q)).coordsOrZero.1))) ∧
      (((P + (2 * j) • Q).coordsOrZero.2 - ((2 * j) • Q).coordsOrZero.2)
          + ((P + (2 * j + 1) • Q).coordsOrZero.2 - ((2 * j + 1) • Q).coordsOrZero.2)
        = ((P + j • (2 • Q)).coordsOrZero.2 - (j • (2 • Q)).coordsOrZero.2)
          + (((P + Q + j • (2 • Q)).coordsOrZero.2 - (j • (2 • Q)).coordsOrZero.2)
            - ((Q + j • (2 • Q)).coordsOrZero.2 - (j • (2 • Q)).coordsOrZero.2))) := by
    intro j _
    have e0 : (2 * j) • Q = j • (2 • Q) := mul_nsmul Q 2 j
    have e1 : (2 * j + 1) • Q = Q + j • (2 • Q) := by rw [add_nsmul, one_nsmul, e0, add_comm]
    have e2 : P + (2 * j + 1) • Q = P + Q + j • (2 • Q) := by rw [e1, add_assoc]
    rw [e2, e1, e0]
    constructor <;> ring
  rw [W.coordsOrZero_veluPointMap2_fullKernelHom h2 Q ρ hρker h₁ hT₁ hgy₁ hΔ₁ P hP,
    hρ P hP2, hρ (P + Q) hPQ2, hρ Q hQ2, Nat.add_sub_cancel]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [sum_Icc_parity_split]
    simp only [one_nsmul]
    rw [Finset.sum_congr rfl (fun j hj => (hsummand j hj).1), Finset.sum_add_distrib,
      Finset.sum_sub_distrib
        (fun j => (P + Q + j • (2 • Q)).coordsOrZero.1 - (j • (2 • Q)).coordsOrZero.1)
        (fun j => (Q + j • (2 • Q)).coordsOrZero.1 - (j • (2 • Q)).coordsOrZero.1)]
    ring
  · dsimp only
    rw [sum_Icc_parity_split]
    simp only [one_nsmul]
    rw [Finset.sum_congr rfl (fun j hj => (hsummand j hj).2), Finset.sum_add_distrib,
      Finset.sum_sub_distrib
        (fun j => (P + Q + j • (2 • Q)).coordsOrZero.2 - (j • (2 • Q)).coordsOrZero.2)
        (fun j => (Q + j • (2 • Q)).coordsOrZero.2 - (j • (2 • Q)).coordsOrZero.2)]
    ring

p2m_export "WeierstrassCurve" "veluPointMap2_comp_fullKernelHom_pinned"

section InterpPolynomial

variable {K : Type*} [Field K] [IsAlgClosed K]

private theorem hstageC_exists_quad_root (b c : K) : ∃ r : K, r ^ 2 + b * r + c = 0 := by
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c : Polynomial K).degree ≠ 0 := by
    have h : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c : Polynomial K)
        = Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c := by
      rw [Polynomial.C_1, one_mul]
    rw [h, Polynomial.degree_quadratic one_ne_zero]
    decide
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨r, ?_⟩
  simpa [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X] using hr

private theorem hstageC_exists_equation_point (W : WeierstrassCurve K) (c : K) :
    ∃ y : K, W.toAffine.Equation c y := by
  obtain ⟨r, hr⟩ := hstageC_exists_quad_root (W.a₁ * c + W.a₃)
    (-(c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆))
  refine ⟨r, (W.toAffine.equation_iff c r).mpr ?_⟩
  linear_combination hr

end InterpPolynomial

section InterpTwoPoints

variable {K : Type*} [Field K]

private theorem hstageC_eq_of_common_points {W W' : WeierstrassCurve K}
    (h1 : W.a₁ = W'.a₁) (h2 : W.a₂ = W'.a₂) (h3 : W.a₃ = W'.a₃)
    {y₀ Y₁ : K} (e0 : W.toAffine.Equation 0 y₀) (e0' : W'.toAffine.Equation 0 y₀)
    (e1 : W.toAffine.Equation 1 Y₁) (e1' : W'.toAffine.Equation 1 Y₁) : W = W' := by
  rw [Affine.equation_iff] at e0 e0' e1 e1'
  have h6 : W.a₆ = W'.a₆ := by linear_combination e0' - e0 + y₀ * h3
  have h4 : W.a₄ = W'.a₄ := by
    linear_combination e1' - e1 + Y₁ * h1 + Y₁ * h3 - h2 - h6
  ext
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h6

end InterpTwoPoints

section CoreC

private theorem _root_.WeierstrassCurve.hstageC_veluQuotient2_eq_fullKernelQuotient_of_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (V : WeierstrassCurve K) [V.IsElliptic] {m : ℕ}
    (hN : ((2 * (m + 1) : ℕ) : K) ≠ 0) (h2 : (2 : K) ≠ 0)
    (R : V.toAffine.Point) (hR : addOrderOf R = 2 * (m + 1))
    (hΔ : (V.fullKernelQuotient R (2 * (m + 1))).Δ ≠ 0)
    (χ : V.toAffine.Point →+ (V.fullKernelQuotient R (2 * (m + 1))).toAffine.Point)
    (hχker : χ.ker = AddSubgroup.zmultiples R)
    (hχ : ∀ P : V.toAffine.Point, P ∉ AddSubgroup.zmultiples R →
      (χ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • R).coordsOrZero.1 - (k • R).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • R).coordsOrZero.2 - (k • R).coordsOrZero.2)))
    (ρ : V.toAffine.Point →+ (V.fullKernelQuotient (2 • R) (m + 1)).toAffine.Point)
    (hρker : ρ.ker = AddSubgroup.zmultiples (2 • R))
    {x₁ y₁ : K} (h₁ : (V.fullKernelQuotient (2 • R) (m + 1)).toAffine.Nonsingular x₁ y₁)
    (hT₁ : ρ R = Point.some x₁ y₁ h₁)
    (hgy₁ : (V.fullKernelQuotient (2 • R) (m + 1)).veluGy x₁ y₁ = 0)
    (hΔ₁ : ((V.fullKernelQuotient (2 • R) (m + 1)).veluQuotient2 x₁ y₁).Δ ≠ 0)
    (hψpin : ∀ P : V.toAffine.Point, P ∉ AddSubgroup.zmultiples R →
      (veluPointMap2 h2 h₁.1 hgy₁ hΔ₁ (ρ P)).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • R).coordsOrZero.1 - (k • R).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • R).coordsOrZero.2 - (k • R).coordsOrZero.2))) :
    (V.fullKernelQuotient (2 • R) (m + 1)).veluQuotient2 x₁ y₁
      = V.fullKernelQuotient R (2 * (m + 1)) := by
  classical
  haveI : NeZero (2 * (m + 1)) := ⟨by omega⟩
  have hχsurj := V.fullKernelHom_surjective_of_isAlgClosed hN R hR χ hχker hχ
  have h2Rmem : 2 • R ∈ AddSubgroup.zmultiples R :=
    AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples R) 2
  have hle : ∀ P' : V.toAffine.Point,
      P' ∈ AddSubgroup.zmultiples (2 • R) → P' ∈ AddSubgroup.zmultiples R := by
    intro P' hP'
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hP'
    rw [← hk]
    exact AddSubgroup.zsmul_mem _ h2Rmem k
  have key : ∀ c : K, ∃ y : K,
      (V.fullKernelQuotient R (2 * (m + 1))).toAffine.Equation c y ∧
      ((V.fullKernelQuotient (2 • R) (m + 1)).veluQuotient2 x₁ y₁).toAffine.Equation c y := by
    intro c
    obtain ⟨yc, hyc⟩ := hstageC_exists_equation_point (V.fullKernelQuotient R (2 * (m + 1))) c
    have hns : (V.fullKernelQuotient R (2 * (m + 1))).toAffine.Nonsingular c yc :=
      ((V.fullKernelQuotient R (2 * (m + 1))).toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        hΔ).mp hyc
    obtain ⟨P₀, hP₀⟩ := hχsurj (Point.some c yc hns)
    have hP₀mem : P₀ ∉ AddSubgroup.zmultiples R := by
      intro hmem
      have h0 : χ P₀ = 0 := by
        rw [← AddMonoidHom.mem_ker, hχker]; exact hmem
      rw [hP₀] at h0
      exact Point.some_ne_zero _ h0
    have hcoords : (χ P₀).coordsOrZero = (c, yc) := by
      rw [hP₀, Point.coordsOrZero_some]
    have hraw := hχ P₀ hP₀mem
    rw [hraw] at hcoords
    have hψ := hψpin P₀ hP₀mem
    rw [hcoords] at hψ
    rcases hv : veluPointMap2 h2 h₁.1 hgy₁ hΔ₁ (ρ P₀) with _ | ⟨u, v, huv⟩
    · exfalso
      rcases eq_zero_or_eq_of_veluPointMap2_eq_zero h2 h₁ hgy₁ hΔ₁ (ρ P₀) hv with h0 | hT
      · have hmem : P₀ ∈ AddSubgroup.zmultiples (2 • R) := by
          rw [← hρker]; exact h0
        exact hP₀mem (hle P₀ hmem)
      · have hPR : ρ (P₀ - R) = 0 := by
          rw [map_sub, hT, ← hT₁, sub_self]
        have hmem : P₀ - R ∈ AddSubgroup.zmultiples (2 • R) := by
          rw [← hρker]; exact hPR
        have hmem' : P₀ ∈ AddSubgroup.zmultiples R := by
          have heq : P₀ = (P₀ - R) + R := by abel
          rw [heq]
          exact AddSubgroup.add_mem _ (hle _ hmem) (AddSubgroup.mem_zmultiples R)
        exact hP₀mem hmem'
    · rw [hv, Point.coordsOrZero_some] at hψ
      injection hψ with hu hv'
      refine ⟨yc, hyc, ?_⟩
      have hEqv := huv.1
      rw [hu, hv'] at hEqv
      exact hEqv
  obtain ⟨Y0, hO0, hT0⟩ := key 0
  obtain ⟨Y1, hO1, hT1⟩ := key 1
  exact hstageC_eq_of_common_points rfl rfl rfl hT0 hO0 hT1 hO1

p2m_export "WeierstrassCurve" "hstageC_veluQuotient2_eq_fullKernelQuotient_of_isAlgClosed"
end CoreC

private theorem hstageK_addOrderOf_map_eq_two
    {F : Type*} [Field F] [DecidableEq F] {W W' : WeierstrassCurve F} {m : ℕ}
    (R : W.toAffine.Point) (hR : addOrderOf R = 2 * (m + 1))
    (ρ : W.toAffine.Point →+ W'.toAffine.Point)
    (hρker : ρ.ker = AddSubgroup.zmultiples (2 • R)) :
    addOrderOf (ρ R) = 2 := by
  have h0 : ρ R ≠ 0 := by
    intro h0
    exact not_mem_zmultiples_two_nsmul R hR (hρker ▸ AddMonoidHom.mem_ker.mpr h0)
  have h2 : 2 • ρ R = 0 := by
    rw [← map_nsmul]
    exact AddMonoidHom.mem_ker.mp (hρker ▸ AddSubgroup.mem_zmultiples (2 • R))
  exact addOrderOf_eq_prime h2 h0

private theorem _root_.WeierstrassCurve.hstageK_ker_comp_eq_zmultiples
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {m : ℕ}
    (h2 : (2 : F) ≠ 0) (R : W.toAffine.Point)
    (ρ : W.toAffine.Point →+ (W.fullKernelQuotient (2 • R) (m + 1)).toAffine.Point)
    (hρker : ρ.ker = AddSubgroup.zmultiples (2 • R))
    {x₁ y₁ : F} (h₁ : (W.fullKernelQuotient (2 • R) (m + 1)).toAffine.Nonsingular x₁ y₁)
    (hT₁ : ρ R = Point.some x₁ y₁ h₁)
    (hgy₁ : (W.fullKernelQuotient (2 • R) (m + 1)).veluGy x₁ y₁ = 0)
    (hΔ₁ : ((W.fullKernelQuotient (2 • R) (m + 1)).veluQuotient2 x₁ y₁).Δ ≠ 0)
    (φ₂ : (W.fullKernelQuotient (2 • R) (m + 1)).toAffine.Point →+
      ((W.fullKernelQuotient (2 • R) (m + 1)).veluQuotient2 x₁ y₁).toAffine.Point)
    (hφ₂ : ⇑φ₂ = veluPointMap2 h2 h₁.1 hgy₁ hΔ₁) :
    (φ₂.comp ρ).ker = AddSubgroup.zmultiples R := by
  have hle : AddSubgroup.zmultiples (2 • R) ≤ AddSubgroup.zmultiples R :=
    AddSubgroup.zmultiples_le_of_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples R) 2)
  apply le_antisymm
  · intro P hP
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, congrFun hφ₂] at hP
    rcases eq_zero_or_eq_of_veluPointMap2_eq_zero h2 h₁ hgy₁ hΔ₁ (ρ P) hP with h0 | hT
    · exact hle (hρker ▸ AddMonoidHom.mem_ker.mpr h0)
    · have hker : P - R ∈ AddSubgroup.zmultiples (2 • R) := by
        rw [← hρker, AddMonoidHom.mem_ker, map_sub, hT, hT₁, sub_self]
      have := AddSubgroup.add_mem _ (hle hker) (AddSubgroup.mem_zmultiples R)
      rwa [sub_add_cancel] at this
  · refine AddSubgroup.zmultiples_le_of_mem (AddMonoidHom.mem_ker.mpr ?_)
    rw [AddMonoidHom.comp_apply, congrFun hφ₂, hT₁,
      veluPointMap2_some_of_eq h2 h₁.1 hgy₁ hΔ₁ h₁ rfl]
    rfl

p2m_export "WeierstrassCurve" "hstageK_ker_comp_eq_zmultiples"

private theorem hstageK_coordsOrZero_equivOfVariableChangeEq_one
    {K : Type*} [Field K] [DecidableEq K] {W : Affine K} {V : Affine K}
    (h : (1 : VariableChange K) • W = V) (Q : V.Point) :
    (Point.equivOfVariableChangeEq h Q).coordsOrZero = Q.coordsOrZero := by
  subst h
  rcases Q with _ | ⟨x, y, hxy⟩
  · rfl
  · show (Point.vcFun 1 W (Point.some x y hxy)).coordsOrZero = _
    simp only [Point.vcFun, Point.coordsOrZero_some, vcX, vcY, VariableChange.one_def,
      Units.val_one, one_pow, one_mul, mul_zero, zero_mul, add_zero]

private theorem hstageK_transportAddEquiv_symm_apply
    {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K) (W : WeierstrassCurve.Affine K)
    {V : WeierstrassCurve.Affine K} (h : C • W = V) (X : V.Point) :
    (transportAddEquiv C W h).symm X = Point.equivOfVariableChangeEq h X := by
  rw [AddEquiv.symm_apply_eq, transportAddEquiv_apply, Equiv.symm_apply_apply]

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_fullKernelHom_eq_veluPointMap2_comp_of_stage_last.WeierstrassCurve"

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (V : WeierstrassCurve K) [V.IsElliptic] {m : ℕ}
    (hN : ((2 * (m + 1) : ℕ) : K) ≠ 0) (h2 : (2 : K) ≠ 0)
    (R : V.toAffine.Point) (hR : addOrderOf R = 2 * (m + 1))
    (hΔ : (V.fullKernelQuotient R (2 * (m + 1))).Δ ≠ 0)
    (χ : V.toAffine.Point →+ (V.fullKernelQuotient R (2 * (m + 1))).toAffine.Point)
    (hχker : χ.ker = AddSubgroup.zmultiples R)
    (hχ : ∀ P : V.toAffine.Point, P ∉ AddSubgroup.zmultiples R →
      (χ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • R).coordsOrZero.1 - (k • R).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • R).coordsOrZero.2 - (k • R).coordsOrZero.2)))
    (ρ : V.toAffine.Point →+ (V.fullKernelQuotient (2 • R) (m + 1)).toAffine.Point)
    (hρker : ρ.ker = AddSubgroup.zmultiples (2 • R))
    (hρ : ∀ P : V.toAffine.Point, P ∉ AddSubgroup.zmultiples (2 • R) →
      (ρ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (m + 1 - 1),
            ((P + k • (2 • R)).coordsOrZero.1 - (k • (2 • R)).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (m + 1 - 1),
            ((P + k • (2 • R)).coordsOrZero.2 - (k • (2 • R)).coordsOrZero.2))) :
    ∃ (x₁ y₁ : K) (h₁ : (V.fullKernelQuotient (2 • R) (m + 1)).toAffine.Nonsingular x₁ y₁)
      (hgy₁ : (V.fullKernelQuotient (2 • R) (m + 1)).veluGy x₁ y₁ = 0)
      (hΔ₁ : ((V.fullKernelQuotient (2 • R) (m + 1)).veluQuotient2 x₁ y₁).Δ ≠ 0)
      (E : VariableChange K)
      (hE : E • V.fullKernelQuotient R (2 * (m + 1))
        = (V.fullKernelQuotient (2 • R) (m + 1)).veluQuotient2 x₁ y₁),
      ρ R = Point.some x₁ y₁ h₁ ∧
      ∀ P : V.toAffine.Point,
        χ P = Point.equivOfVariableChangeEq hE (veluPointMap2 h2 h₁.1 hgy₁ hΔ₁ (ρ P)) := by
  classical

  have hN' : (2 : K) * ((m : K) + 1) ≠ 0 := by push_cast at hN; exact hN
  have hm1 : ((m + 1 : ℕ) : K) ≠ 0 := by push_cast; exact (mul_ne_zero_iff.mp hN').2
  have h2R : addOrderOf (2 • R) = m + 1 := by
    have h0 : (m + 1) • (2 • R) = 0 := by
      rw [← mul_nsmul', mul_comm, ← hR, addOrderOf_nsmul_eq_zero]
    have h2d : addOrderOf R ∣ 2 * addOrderOf (2 • R) := by
      rw [addOrderOf_dvd_iff_nsmul_eq_zero, mul_comm, mul_nsmul', addOrderOf_nsmul_eq_zero]
    rw [hR] at h2d
    exact Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero h0)
      ((mul_dvd_mul_iff_left two_ne_zero).mp h2d)

  haveI hV₁Δ : (V.fullKernelQuotient (2 • R) (m + 1)).Δ ≠ 0 :=
    fullKernelQuotient_discriminant_ne_zero (m + 1) V hm1 (2 • R) h2R
  haveI hV₁ : (V.fullKernelQuotient (2 • R) (m + 1)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hV₁Δ⟩

  have hρR2 : addOrderOf (ρ R) = 2 := hstageK_addOrderOf_map_eq_two R hR ρ hρker
  have hρR2' : addOrderOf (ρ R) = 2 * (0 + 1) := by omega

  have hN2 : ((2 * (0 + 1) : ℕ) : K) ≠ 0 := by
    have heq : ((2 * (0 + 1) : ℕ) : K) = 2 := by push_cast; ring
    rw [heq]; exact h2
  obtain ⟨-, -, x₁, y₁, h₁, hT₁', hgy₁, hΔ₁⟩ :=
    (V.fullKernelQuotient (2 • R) (m + 1)).exists_two_torsion_data hN2 (ρ R) hρR2'
  have hT₁ : ρ R = Point.some x₁ y₁ h₁ := by rwa [one_nsmul] at hT₁'

  obtain ⟨φ₂, hφ₂⟩ :=
    (V.fullKernelQuotient (2 • R) (m + 1)).exists_addMonoidHom_coe_eq_veluPointMap2 h2 h₁.1 hgy₁ hΔ₁

  have hP3 := V.veluPointMap2_comp_fullKernelHom_pinned h2 R ρ hρker hρ h₁ hT₁ hgy₁ hΔ₁

  have hC := V.hstageC_veluQuotient2_eq_fullKernelQuotient_of_isAlgClosed hN h2 R hR hΔ
    χ hχker hχ ρ hρker h₁ hT₁ hgy₁ hΔ₁ hP3

  refine ⟨x₁, y₁, h₁, hgy₁, hΔ₁, 1, (one_smul _ _).trans hC.symm, hT₁, ?_⟩
  intro P
  set hE : (1 : VariableChange K) • V.fullKernelQuotient R (2 * (m + 1))
    = (V.fullKernelQuotient (2 • R) (m + 1)).veluQuotient2 x₁ y₁ := (one_smul _ _).trans hC.symm

  set ψ : V.toAffine.Point →+ (V.fullKernelQuotient R (2 * (m + 1))).toAffine.Point :=
    ((transportAddEquiv 1 _ hE).symm : _ ≃+ _).toAddMonoidHom.comp (φ₂.comp ρ) with hψdef
  have hψeq : ∀ Q, ψ Q = Point.equivOfVariableChangeEq hE (veluPointMap2 h2 h₁.1 hgy₁ hΔ₁ (ρ Q)) := by
    intro Q
    rw [hψdef]
    simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    rw [hstageK_transportAddEquiv_symm_apply 1 _ hE (φ₂ (ρ Q)), congrFun hφ₂]

  have hK3 := V.hstageK_ker_comp_eq_zmultiples h2 R ρ hρker h₁ hT₁ hgy₁ hΔ₁ φ₂ hφ₂
  have hψker : ψ.ker = AddSubgroup.zmultiples R := by
    rw [← hK3, hψdef]
    ext Q
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, EmbeddingLike.map_eq_zero_iff]

  have hψcoords : ∀ P' : V.toAffine.Point, P' ∉ AddSubgroup.zmultiples R →
      (χ P').coordsOrZero = (ψ P').coordsOrZero := by
    intro P' hP'
    rw [hχ P' hP', hψeq P', hstageK_coordsOrZero_equivOfVariableChangeEq_one hE _, hP3 P' hP']

  have hU := addMonoidHom_eq_of_ker_eq_of_coordsOrZero_eq R χ ψ hχker hψker hψcoords
  rw [hU, hψeq P]

end S_WeierstrassCurve_fullKernelHom_eq_veluPointMap2_comp_of_stage_last
end P2MW
export P2MW.S_WeierstrassCurve_fullKernelHom_eq_veluPointMap2_comp_of_stage_last (solution)
