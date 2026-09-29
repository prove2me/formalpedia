-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ac8bbd1e-56df-5cd8-9add-13653aa77261

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Theorems.Thm_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_reduceHom_apply_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.kohelW_one Polynomial.rootESymm_zero_right WeierstrassCurve.kohelQuotient_a₂ WeierstrassCurve.kohelQuotient_a₃ WeierstrassCurve.kohelT_one WeierstrassCurve.kohelQuotient_one WeierstrassCurve.kohelQuotient_a₁ Polynomial.rootESymm_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.legendreVariableChange_s WeierstrassCurve.legendreVariableChange_t WeierstrassCurve.legendreVariableChange_r WeierstrassCurve.legendreVariableChange_u ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.deuringVariableChange_s WeierstrassCurve.deuringVariableChange_t WeierstrassCurve.deuringCurve_a₄ WeierstrassCurve.deuringCurve_a₂ WeierstrassCurve.deuringCurve_a₆ WeierstrassCurve.deuringCurve_a₁ WeierstrassCurve.deuringVariableChange_u WeierstrassCurve.deuringCurve_a₃ WeierstrassCurve.deuringVariableChange_r WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "IsLocalRing WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate Pointwise

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ map_map a₁ map isElliptic_iff Affine.Point.some reduction map_id toAffine Affine.Point map_injective map_Δ Δ VariableChange Affine.Point.neg_some baseChange evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet reduceHom Affine.Y_mem_of_X_mem map_residue_Δ_ne_zero_iff reducePoint reducePoint_some_of_mem reducePoint_some_of_notMem Affine.Point.equivOfVariableChangeEq ratPointHom pointAddEquivOfEq pointAddEquivOfEq_some exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j exists_mem_rationalHomSet_eq_smul_of_forall_reduceHom_apply_eq_zero exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet Affine.Point.vcInvFun_add card_torsion_of_isAlgClosed"
namespace DeuringLiftPlaceV2
p2m_open "WeierstrassCurve"

section VC

variable {K : Type*} [Field K] [DecidableEq K]

theorem equivOfVariableChangeEq_symm_some_congr (v : VariableChange K) {V₁ V₂ W : WeierstrassCurve K}
    (h12 : V₁ = V₂) (h₁ : v • V₁ = W) (h₂ : v • V₂ = W) {x y : K}
    (hn₁ : V₁.toAffine.Nonsingular x y) (hn₂ : V₂.toAffine.Nonsingular x y) :
    (Affine.Point.equivOfVariableChangeEq (W := V₁) h₁).symm (.some x y hn₁) =
      (Affine.Point.equivOfVariableChangeEq (W := V₂) h₂).symm (.some x y hn₂) := by
  subst h12
  rfl

theorem equivOfVariableChangeEq_symm_zero (v : VariableChange K) {V W : WeierstrassCurve K}
    (h : v • V = W) :
    (Affine.Point.equivOfVariableChangeEq (W := V) h).symm 0 = 0 := by
  subst h
  rfl

end VC

section RatPoint

variable {F k : Type} [Field F] [Field k] [DecidableEq F] [DecidableEq k]

@[scoped simp] theorem ratPointHom_apply_zero (f : F →+* k) (W₀ : WeierstrassCurve F) :
    ratPointHom f (W₀ := W₀) 0 = 0 := rfl

theorem ratPointHom_apply_some (f : F →+* k) {W₀ : WeierstrassCurve F} {x y : F}
    (h : W₀.toAffine.Nonsingular x y) :
    ratPointHom f (W₀ := W₀) (.some x y h) =
      .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

end RatPoint

section Transport

variable {A A' : ValuationSubring (AlgebraicClosure ℚ)}
  (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ • A' = A)

local notation "ℚbar" => AlgebraicClosure ℚ

include hτ in
theorem mem_of_mem (x : ℚbar) (hx : x ∈ A') : τ x ∈ A := by
  have h := ValuationSubring.smul_mem_pointwise_smul τ x A' hx
  rwa [hτ, AlgEquiv.smul_def] at h

include hτ in
theorem mem_iff (x : ℚbar) : τ x ∈ A ↔ x ∈ A' := by
  refine ⟨fun h => ?_, mem_of_mem τ hτ x⟩
  have h' : τ • x ∈ τ • A' := by rwa [hτ, AlgEquiv.smul_def]
  exact ValuationSubring.smul_mem_pointwise_smul_iff.mp h'

include hτ in
theorem symm_mem_of_mem (y : ℚbar) (hy : y ∈ A) : τ.symm y ∈ A' := by
  rw [← mem_iff τ hτ]
  simpa using hy

def ringEquivOfSMulEq : A' ≃+* A where
  toFun x := ⟨τ x, mem_of_mem τ hτ x x.2⟩
  invFun y := ⟨τ.symm y, symm_mem_of_mem τ hτ y y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_ringEquivOfSMulEq_apply (x : A') :
    ((ringEquivOfSMulEq τ hτ x : A) : ℚbar) = τ x := rfl

variable (E : WeierstrassCurve A')

def twist : WeierstrassCurve A := E.map (ringEquivOfSMulEq τ hτ).toRingHom

theorem twist_map_subtype :
    (twist τ hτ E).map A.subtype = (E.map A'.subtype).map (τ : ℚbar →+* ℚbar) := by
  simp only [twist, WeierstrassCurve.map_map]
  congr 1

theorem map_symm_twist_map_subtype :
    ((twist τ hτ E).map A.subtype).map (τ.symm : ℚbar →+* ℚbar) = E.map A'.subtype := by
  rw [twist_map_subtype, WeierstrassCurve.map_map]
  have : ((τ.symm : ℚbar →+* ℚbar).comp (τ : ℚbar →+* ℚbar)) = RingHom.id _ := by
    ext x; simp
  rw [this, WeierstrassCurve.map_map]
  rfl

variable (e : ResidueField A' ≃+* ResidueField A)
  (hres : ∀ x : A', residue A (ringEquivOfSMulEq τ hτ x) = e (residue A' x))

include hres in

theorem twist_map_residue :
    (twist τ hτ E).map (residue A) = (E.map (residue A')).map e.toRingHom := by
  simp only [twist, WeierstrassCurve.map_map]
  congr 1
  ext x
  exact hres x

include hres in
theorem twist_Δ_ne_zero (hΔ : (E.map (residue A')).Δ ≠ 0) :
    ((twist τ hτ E).map (residue A)).Δ ≠ 0 := by
  rw [twist_map_residue τ hτ E e hres, WeierstrassCurve.map_Δ]
  simpa using hΔ

variable [DecidableEq ℚbar]

def T : (E.map A'.subtype).toAffine.Point →+ ((twist τ hτ E).map A.subtype).toAffine.Point :=
  (pointAddEquivOfEq (twist_map_subtype τ hτ E).symm).toAddMonoidHom.comp
    (ratPointHom (τ : ℚbar →+* ℚbar))

def T' : ((twist τ hτ E).map A.subtype).toAffine.Point →+ (E.map A'.subtype).toAffine.Point :=
  (pointAddEquivOfEq (map_symm_twist_map_subtype τ hτ E)).toAddMonoidHom.comp
    (ratPointHom (τ.symm : ℚbar →+* ℚbar))

theorem T_zero : T τ hτ E 0 = 0 := map_zero _

private theorem some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem T_some {x y : ℚbar} (h : (E.map A'.subtype).toAffine.Nonsingular x y) :
    ∃ h', T τ hτ E (.some x y h) = .some (τ x) (τ y) h' := by
  have h1 : ((twist τ hτ E).map A.subtype).toAffine.Nonsingular (τ x) (τ y) := by
    rw [twist_map_subtype]
    exact ((E.map A'.subtype).toAffine.map_nonsingular (τ : ℚbar →+* ℚbar).injective x y).mpr h
  refine ⟨h1, ?_⟩
  simp only [T, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ratPointHom_apply_some]
  rw [pointAddEquivOfEq_some]
  exact some_congr rfl rfl _ _

theorem T'_some {x y : ℚbar} (h : ((twist τ hτ E).map A.subtype).toAffine.Nonsingular x y) :
    ∃ h', T' τ hτ E (.some x y h) = .some (τ.symm x) (τ.symm y) h' := by
  have h1 : (E.map A'.subtype).toAffine.Nonsingular (τ.symm x) (τ.symm y) := by
    rw [← map_symm_twist_map_subtype τ hτ E]
    exact (((twist τ hτ E).map A.subtype).toAffine.map_nonsingular
      (τ.symm : ℚbar →+* ℚbar).injective x y).mpr h
  refine ⟨h1, ?_⟩
  simp only [T', AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    ratPointHom_apply_some]
  rw [pointAddEquivOfEq_some]
  exact some_congr rfl rfl _ _

theorem T_T' (P : ((twist τ hτ E).map A.subtype).toAffine.Point) : T τ hτ E (T' τ hτ E P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · show T τ hτ E (T' τ hτ E 0) = 0
    rw [map_zero, map_zero]
  · obtain ⟨h', e'⟩ := T'_some τ hτ E h
    rw [e']
    obtain ⟨h'', e''⟩ := T_some τ hτ E h'
    rw [e'']
    exact some_congr (by simp) (by simp) _ _

theorem T'_T (P : (E.map A'.subtype).toAffine.Point) : T' τ hτ E (T τ hτ E P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · show T' τ hτ E (T τ hτ E 0) = 0
    rw [map_zero, map_zero]
  · obtain ⟨h', e'⟩ := T_some τ hτ E h
    rw [e']
    obtain ⟨h'', e''⟩ := T'_some τ hτ E h'
    rw [e'']
    exact some_congr (by simp) (by simp) _ _

theorem T_surjective : Function.Surjective (T τ hτ E) :=
  fun P => ⟨T' τ hτ E P, T_T' τ hτ E P⟩

def conj (α : (E.map A'.subtype).toAffine.Point →+ (E.map A'.subtype).toAffine.Point) :
    ((twist τ hτ E).map A.subtype).toAffine.Point →+ ((twist τ hτ E).map A.subtype).toAffine.Point :=
  (T τ hτ E).comp (α.comp (T' τ hτ E))

theorem conj_apply_T (α : (E.map A'.subtype).toAffine.Point →+ (E.map A'.subtype).toAffine.Point)
    (P : (E.map A'.subtype).toAffine.Point) :
    conj τ hτ E α (T τ hτ E P) = T τ hτ E (α P) := by
  simp [conj, T'_T]

omit hτ in

theorem evalEvalBC_self (p : ℚbar[X][Y]) (x y : ℚbar) :
    evalEvalBC ℚbar p x y = p.evalEval x y := by
  simp only [evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]

omit hτ in
theorem evalEvalBC_map (p : ℚbar[X][Y]) (x y : ℚbar) :
    evalEvalBC ℚbar (p.map (mapRingHom (τ : ℚbar →+* ℚbar))) (τ x) (τ y) =
      τ (evalEvalBC ℚbar p x y) := by
  rw [evalEvalBC_self, evalEvalBC_self]
  exact Polynomial.map_mapRingHom_evalEval (τ : ℚbar →+* ℚbar) p x y

theorem conj_mem_rationalHomSet
    {α : (E.map A'.subtype).toAffine.Point →+ (E.map A'.subtype).toAffine.Point}
    (hα : α ∈ rationalHomSet ℚbar (E.map A'.subtype) (E.map A'.subtype)) :
    conj τ hτ E α ∈ rationalHomSet ℚbar ((twist τ hτ E).map A.subtype) ((twist τ hτ E).map A.subtype) := by
  rcases hα with hα | ⟨nX, dX, nY, dY, B, hB, H⟩
  · left
    subst hα
    ext P
    show T τ hτ E 0 = 0
    exact map_zero _
  right
  refine ⟨nX.map (mapRingHom (τ : ℚbar →+* ℚbar)), dX.map (mapRingHom (τ : ℚbar →+* ℚbar)),
    nY.map (mapRingHom (τ : ℚbar →+* ℚbar)), dY.map (mapRingHom (τ : ℚbar →+* ℚbar)),
    τ '' B, hB.image _, ?_⟩
  intro x' y' h' hx'

  obtain ⟨h, hT'⟩ := T'_some τ hτ E (x := x') (y := y') h'
  obtain ⟨x, hx⟩ : ∃ x, x = τ.symm x' := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = τ.symm y' := ⟨_, rfl⟩
  subst hx hy
  have hxx : τ (τ.symm x') = x' := by simp
  have hyy : τ (τ.symm y') = y' := by simp
  have hxB : τ.symm x' ∉ B := by
    intro hmem
    exact hx' ⟨τ.symm x', hmem, hxx⟩
  obtain ⟨hdX, hdY, h'', hαP⟩ := H (τ.symm x') (τ.symm y') h hxB
  have key0 : conj τ hτ E α (.some x' y' h') = T τ hτ E (α (.some (τ.symm x') (τ.symm y') h)) := by
    simp only [conj, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hT']
  obtain ⟨h3, hT⟩ := T_some τ hτ E h''
  have key : conj τ hτ E α (.some x' y' h') = _ := (key0.trans (congrArg (T τ hτ E) hαP)).trans hT
  have edX : evalEvalBC ℚbar (dX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' = τ (evalEvalBC ℚbar dX (τ.symm x') (τ.symm y')) := by
    have hh := evalEvalBC_map τ dX (τ.symm x') (τ.symm y')
    rwa [hxx, hyy] at hh
  have edY : evalEvalBC ℚbar (dY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' = τ (evalEvalBC ℚbar dY (τ.symm x') (τ.symm y')) := by
    have hh := evalEvalBC_map τ dY (τ.symm x') (τ.symm y')
    rwa [hxx, hyy] at hh
  have enX : evalEvalBC ℚbar (nX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' = τ (evalEvalBC ℚbar nX (τ.symm x') (τ.symm y')) := by
    have hh := evalEvalBC_map τ nX (τ.symm x') (τ.symm y')
    rwa [hxx, hyy] at hh
  have enY : evalEvalBC ℚbar (nY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' = τ (evalEvalBC ℚbar nY (τ.symm x') (τ.symm y')) := by
    have hh := evalEvalBC_map τ nY (τ.symm x') (τ.symm y')
    rwa [hxx, hyy] at hh
  refine ⟨by rw [edX]; simpa using hdX, by rw [edY]; simpa using hdY, ?_⟩
  have hcoordX : τ (evalEvalBC ℚbar nX (τ.symm x') (τ.symm y') / evalEvalBC ℚbar dX (τ.symm x') (τ.symm y')) =
      evalEvalBC ℚbar (nX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' / evalEvalBC ℚbar (dX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' := by
    rw [map_div₀, enX, edX]
  have hcoordY : τ (evalEvalBC ℚbar nY (τ.symm x') (τ.symm y') / evalEvalBC ℚbar dY (τ.symm x') (τ.symm y')) =
      evalEvalBC ℚbar (nY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' / evalEvalBC ℚbar (dY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' := by
    rw [map_div₀, enY, edY]
  have h4 : ((twist τ hτ E).map A.subtype).toAffine.Nonsingular
      (evalEvalBC ℚbar (nX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' / evalEvalBC ℚbar (dX.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y')
      (evalEvalBC ℚbar (nY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y' / evalEvalBC ℚbar (dY.map (mapRingHom (τ : ℚbar →+* ℚbar))) x' y') := by
    rw [← hcoordX, ← hcoordY]; exact h3
  refine ⟨h4, key.trans ?_⟩
  exact some_congr hcoordX hcoordY _ _

variable [DecidableEq (ResidueField A)] [DecidableEq (ResidueField A')]

include hres in

theorem reduce_T {W : WeierstrassCurve (ResidueField A)} (v : VariableChange (ResidueField A))
    (hΔ : (E.map (residue A')).Δ ≠ 0)
    (hΔ' : ((twist τ hτ E).map (residue A)).Δ ≠ 0)
    (hv : v • (E.map (residue A')).map e.toRingHom = W)
    (hv' : v • (twist τ hτ E).map (residue A) = W)
    (Q : (E.map A'.subtype).toAffine.Point) :
    (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (T τ hτ E Q)) =
      (Affine.Point.equivOfVariableChangeEq hv).symm (ratPointHom e.toRingHom (reduceHom hΔ Q)) := by
  have hcurve := twist_map_residue τ hτ E e hres
  rcases Q with _ | ⟨x, y, h⟩
  · show (Affine.Point.equivOfVariableChangeEq hv').symm (reduceHom hΔ' (T τ hτ E 0)) =
      (Affine.Point.equivOfVariableChangeEq hv).symm (ratPointHom e.toRingHom (reduceHom hΔ 0))
    rw [T_zero, map_zero (reduceHom hΔ'), map_zero (reduceHom hΔ), map_zero (ratPointHom e.toRingHom),
      equivOfVariableChangeEq_symm_zero, equivOfVariableChangeEq_symm_zero]
  · obtain ⟨h', hT⟩ := T_some τ hτ E h
    rw [hT]
    have e1 : reduceHom hΔ' (.some (τ x) (τ y) h') = reducePoint hΔ' (.some (τ x) (τ y) h') := rfl
    have e2 : reduceHom hΔ (.some x y h) = reducePoint hΔ (.some x y h) := rfl
    rw [e1, e2]
    by_cases hx : x ∈ A'
    · have hτx : τ x ∈ A := mem_of_mem τ hτ x hx
      rw [reducePoint_some_of_mem hΔ' h' hτx, reducePoint_some_of_mem hΔ h hx, ratPointHom_apply_some]
      have hy : y ∈ A' := Affine.Y_mem_of_X_mem E h.1 hx
      have hτy : τ y ∈ A := mem_of_mem τ hτ y hy
      have ex : residue A ⟨τ x, hτx⟩ = e.toRingHom (residue A' ⟨x, hx⟩) := hres ⟨x, hx⟩
      have ey : residue A ⟨τ y, hτy⟩ = e.toRingHom (residue A' ⟨y, hy⟩) := hres ⟨y, hy⟩
      have step : ∀ (a b : ResidueField A)
          (h₁ : ((twist τ hτ E).map (residue A)).toAffine.Nonsingular a b)
          (a' b' : ResidueField A) (ha : a = a') (hb : b = b')
          (h₂ : ((E.map (residue A')).map e.toRingHom).toAffine.Nonsingular a' b'),
          (Affine.Point.equivOfVariableChangeEq hv').symm (.some a b h₁) =
            (Affine.Point.equivOfVariableChangeEq hv).symm (.some a' b' h₂) := by
        intro a b h₁ a' b' ha hb h₂
        subst ha hb
        exact equivOfVariableChangeEq_symm_some_congr v hcurve hv' hv h₁ h₂
      exact step _ _ _ _ _ ex ey _
    · have hτx : τ x ∉ A := fun hmem => hx ((mem_iff τ hτ x).mp hmem)
      rw [reducePoint_some_of_notMem hΔ' h' hτx, reducePoint_some_of_notMem hΔ h hx,
        map_zero (ratPointHom e.toRingHom), equivOfVariableChangeEq_symm_zero,
        equivOfVariableChangeEq_symm_zero]

end Transport

section HomSet

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]

theorem isRationallyRepresented_neg_id (W : WeierstrassCurve F) :
    IsRationallyRepresented k W W (-(AddMonoidHom.id _)) := by
  refine ⟨C X, 1, -X - C (C W.a₁ * X + C W.a₃), 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : F[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C X : F[X][Y]) x y = x := by simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC k (-X - C (C W.a₁ * X + C W.a₃) : F[X][Y]) x y =
      (W.baseChange k).toAffine.negY x y := by
    simp [evalEvalBC, Polynomial.evalEval, Affine.negY, WeierstrassCurve.baseChange]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, e1, e2, div_one, div_one, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    Affine.Point.neg_some]
  exact ⟨_, rfl⟩

theorem neg_id_mem_rationalHomSet (W : WeierstrassCurve F) :
    (-(AddMonoidHom.id _) : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W :=
  Or.inr (isRationallyRepresented_neg_id k W)

variable {k}

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) : -α ∈ rationalHomSet k W₁ W₂ := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet k W₁ W₂ W₂ hα (neg_id_mem_rationalHomSet k W₂)
  have e : (-(AddMonoidHom.id _)).comp α = -α := by ext P; simp
  rwa [e] at h

variable [IsAlgClosed k]

theorem sub_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hβ : β ∈ rationalHomSet k W₁ W₂) :
    α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet hβ)

theorem zsmul_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (n : ℤ) : n • α ∈ rationalHomSet k W₁ W₂ := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih =>
    rw [add_zsmul, one_zsmul]
    exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ ih hα
  | pred n ih =>
    rw [sub_zsmul, one_zsmul]
    exact sub_mem_rationalHomSet ih hα

theorem zsmul_id_mem_rationalHomSet (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ) :
    (n • AddMonoidHom.id _ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W :=
  zsmul_mem_rationalHomSet (id_mem_rationalHomSet k W) n

theorem affine_mem_rationalHomSet {W : WeierstrassCurve F} [W.IsElliptic]
    {α : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W W) (N M : ℤ) :
    N • AddMonoidHom.id _ + M • α ∈ rationalHomSet k W W :=
  WeierstrassCurve.add_mem_rationalHomSet k W W (zsmul_id_mem_rationalHomSet W N)
    (zsmul_mem_rationalHomSet hα M)

end HomSet

section Model

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem isElliptic_map_subtype (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) :
    (E.map A.subtype).IsElliptic := by
  have hu : IsUnit E.Δ := (map_residue_Δ_ne_zero_iff E).mp hΔ
  rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
  exact hu.map A.subtype

variable {K : Type*} [Field K] [DecidableEq K]

theorem equivOfVariableChangeEq_symm_add (C : VariableChange K) (X : WeierstrassCurve.Affine K)
    {V : WeierstrassCurve.Affine K} (h : C • X = V) (P Q : X.Point) :
    (Affine.Point.equivOfVariableChangeEq h).symm (P + Q) =
      (Affine.Point.equivOfVariableChangeEq h).symm P + (Affine.Point.equivOfVariableChangeEq h).symm Q := by
  subst h
  exact WeierstrassCurve.Affine.Point.vcInvFun_add C X P Q

def vStar (C : VariableChange K) (X : WeierstrassCurve.Affine K)
    {V : WeierstrassCurve.Affine K} (h : C • X = V) : X.Point →+ V.Point :=
  AddMonoidHom.mk' (fun P => (Affine.Point.equivOfVariableChangeEq h).symm P)
    (equivOfVariableChangeEq_symm_add C X h)

@[scoped simp] theorem vStar_apply (C : VariableChange K) (X : WeierstrassCurve.Affine K)
    {V : WeierstrassCurve.Affine K} (h : C • X = V) (P : X.Point) :
    vStar C X h P = (Affine.Point.equivOfVariableChangeEq h).symm P := rfl

end Model

section Lift

variable (A : ValuationSubring (AlgebraicClosure ℚ))
  [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (ResidueField A)]

local notation "ℚbar" => AlgebraicClosure ℚ

def Liftable (W : WeierstrassCurve (ResidueField A)) (α₀ : W.toAffine.Point →+ W.toAffine.Point) :
    Prop :=
  ∃ (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) (v : VariableChange (ResidueField A))
    (hv : v • E.map (residue A) = W),
    ∃ α ∈ rationalHomSet ℚbar (E.map A.subtype) (E.map A.subtype),
      ∀ P : (E.map A.subtype).toAffine.Point,
        (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ (α P)) =
          α₀ ((Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ P))

variable {A}

theorem Liftable.affine {W : WeierstrassCurve (ResidueField A)}
    {β₀ : W.toAffine.Point →+ W.toAffine.Point}
    (h : Liftable A W β₀) (N M : ℤ) : Liftable A W (N • AddMonoidHom.id _ + M • β₀) := by
  obtain ⟨E, hΔ, v, hv, β, hβ, hcomm⟩ := h
  haveI := isElliptic_map_subtype E hΔ
  refine ⟨E, hΔ, v, hv, N • AddMonoidHom.id _ + M • β, ?_, fun P => ?_⟩
  · exact affine_mem_rationalHomSet (k := ℚbar) (W := E.map A.subtype) hβ N M
  · set T : ((E.map A.subtype).baseChange ℚbar).toAffine.Point →+ W.toAffine.Point :=
      (vStar v (E.map (residue A)) hv).comp (reduceHom hΔ) with hT
    have hT' : ∀ Q, (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ Q) = T Q :=
      fun Q => rfl
    have hcomm' : ∀ Q, T (β Q) = β₀ (T Q) := fun Q => by rw [← hT', ← hT']; exact hcomm Q
    rw [hT', hT']
    simp only [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, map_add,
      map_zsmul, hcomm']

theorem Liftable.of_two_smul {W : WeierstrassCurve (ResidueField A)} [W.IsElliptic]
    {α₀ : W.toAffine.Point →+ W.toAffine.Point} (h2 : (2 : ResidueField A) ≠ 0)
    (h : Liftable A W ((2 : ℤ) • α₀)) : Liftable A W α₀ := by
  obtain ⟨E, hΔ, v, hv, γ, hγ, hcomm⟩ := h
  haveI hEell := isElliptic_map_subtype E hΔ
  set T : ((E.map A.subtype).baseChange ℚbar).toAffine.Point →+ W.toAffine.Point :=
    (vStar v (E.map (residue A)) hv).comp (reduceHom hΔ) with hT
  have hT' : ∀ Q, (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ Q) = T Q :=
    fun Q => rfl
  have hcomm' : ∀ Q, T (γ Q) = ((2 : ℤ) • α₀) (T Q) := fun Q => by
    rw [← hT', ← hT']; exact hcomm Q

  have hker : ∀ P : (E.map A.subtype).toAffine.Point, ((2 : ℕ) : ℤ) • P = 0 →
      reduceHom hΔ (γ P) = 0 := by
    intro P hP
    have e3 : ((2 : ℕ) : ℤ) • (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ P) = 0 := by
      rw [← vStar_apply, ← map_zsmul, ← map_zsmul, hP, map_zero, map_zero]
    have e2 : (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ (γ P)) = 0 := by
      rw [hcomm P, AddMonoidHom.zsmul_apply, ← map_zsmul α₀]
      norm_num at e3
      rw [e3, map_zero]
    exact (Affine.Point.equivOfVariableChangeEq hv).symm.injective
      (e2.trans (equivOfVariableChangeEq_symm_zero v hv).symm)
  have h2' : ((2 : ℕ) : ResidueField A) ≠ 0 := by exact_mod_cast h2
  obtain ⟨δ, hδ, hγδ⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_reduceHom_apply_eq_zero
      E E hΔ h2' hγ hker
  refine ⟨E, hΔ, v, hv, δ, hδ, fun P => ?_⟩

  have h2id : ((2 : ℤ) • AddMonoidHom.id _ :
      ((E.map A.subtype).baseChange ℚbar).toAffine.Point →+
        ((E.map A.subtype).baseChange ℚbar).toAffine.Point) ≠ 0 := by
    intro h0
    have h3 : ((3 : ℕ) : ℚbar) ≠ 0 := by norm_num
    have hcard : Nat.card (Submodule.torsionBy ℤ
        ((E.map A.subtype).baseChange ℚbar).toAffine.Point ((3 : ℕ) : ℤ)) = 3 ^ 2 :=
      WeierstrassCurve.card_torsion_of_isAlgClosed (K := ℚbar) (E.map A.subtype) h3
    set Tor := Submodule.torsionBy ℤ ((E.map A.subtype).baseChange ℚbar).toAffine.Point
      ((3 : ℕ) : ℤ) with hTor
    haveI : Finite Tor := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hnt : Nontrivial Tor := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]; norm_num
    obtain ⟨⟨R, hR⟩, hR1⟩ := exists_ne (0 : Tor)
    have hR3 : ((3 : ℕ) : ℤ) • R = 0 := (Submodule.mem_torsionBy_iff _ _).mp hR
    have hR2 : (2 : ℤ) • R = 0 := by
      have := congrArg (fun f => f R) h0
      simpa using this
    have hR0 : R = 0 := by
      have e : R = ((3 : ℕ) : ℤ) • R - (2 : ℤ) • R := by simp only [Nat.cast_ofNat]; module
      rw [e, hR3, hR2, sub_zero]
    exact hR1 (Subtype.ext hR0)
  obtain ⟨P', hP'⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet ℚbar
    (zsmul_id_mem_rationalHomSet (k := ℚbar) (E.map A.subtype) 2) h2id P
  have hP : P = (2 : ℤ) • P' := by rw [← hP']; rfl
  have hδP : δ P = γ P' := by
    rw [hP, map_zsmul]; exact (hγδ P').symm
  rw [hδP, hT', hT', hcomm', AddMonoidHom.zsmul_apply, ← map_zsmul, ← map_zsmul, ← hP]

end Lift

section Arith

theorem disc_ne_zero {t q : ℤ} (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) : t ^ 2 - 4 * q ≠ 0 := by
  intro hD
  have ht2 : Even (t ^ 2) := ⟨2 * q, by linarith⟩
  have ht : Even t := (Int.even_pow' two_ne_zero).mp ht2
  obtain ⟨u, rfl⟩ := ht
  have hq : q = u ^ 2 := by nlinarith
  exact hirr u (by rw [hq]; ring)

theorem exists_not_dvd_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (T Q : ℤ) :
    ∃ a₀ : ℤ, ¬ (p : ℤ) ∣ a₀ ^ 2 + T * a₀ + Q := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hd : (p : ℤ) ∣ (2 ^ 2 + T * 2 + Q) - (1 ^ 2 + T * 1 + Q) - ((1 ^ 2 + T * 1 + Q) -
      (0 ^ 2 + T * 0 + Q)) := dvd_sub (dvd_sub h2 h1) (dvd_sub h1 h0)
  have h2' : (p : ℤ) ∣ (2 : ℕ) := by convert hd using 1; ring
  have hp2' : p ∣ 2 := by exact_mod_cast h2'
  rcases (Nat.dvd_prime Nat.prime_two).mp hp2' with h | h
  · exact hp.one_lt.ne' h
  · exact hp2 h

theorem exists_not_two_dvd {t q : ℤ} (h : ¬ (Odd t ∧ Even q)) :
    ∃ a₀ : ℤ, ¬ (2 : ℤ) ∣ a₀ ^ 2 + t * a₀ + q := by
  by_cases hq : Even q
  · have ht : Even t := by
      by_contra ht
      exact h ⟨Int.not_even_iff_odd.mp ht, hq⟩
    refine ⟨1, ?_⟩
    intro hd
    have : Even (1 ^ 2 + t * 1 + q) := even_iff_two_dvd.mpr hd
    have h1 : Even (t * 1 + q) := (Even.mul_right ht 1).add hq
    have : Even ((1 ^ 2 + t * 1 + q) - (t * 1 + q)) := Int.even_sub.mpr (iff_of_true this h1)
    norm_num at this
  · refine ⟨0, ?_⟩
    intro hd
    apply hq
    simpa using (even_iff_two_dvd.mpr hd)

theorem hirr_one {t q : ℤ} (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) (a : ℤ) :
    ∀ x : ℤ, x ^ 2 - (2 * a + (1 : ℕ) * t) * x + (a ^ 2 + (1 : ℕ) * t * a + (1 : ℕ) ^ 2 * q) ≠ 0 := by
  intro x hx
  apply hirr (x - a)
  rw [← hx]; push_cast; ring

theorem hirr_two {t q : ℤ} (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) (a : ℤ) :
    ∀ x : ℤ, x ^ 2 - (2 * a + (2 : ℕ) * t) * x + (a ^ 2 + (2 : ℕ) * t * a + (2 : ℕ) ^ 2 * q) ≠ 0 := by
  intro x hx
  push_cast at hx

  have hz : (x - a) ^ 2 - 2 * t * (x - a) + 4 * q = 0 := by rw [← hx]; ring
  have hz2 : Even ((x - a) ^ 2) := ⟨t * (x - a) - 2 * q, by linarith⟩
  obtain ⟨w, hw⟩ := (Int.even_pow' two_ne_zero).mp hz2
  apply hirr w
  have h4 : (4 : ℤ) * (w ^ 2 - t * w + q) = 0 := by rw [← hz, hw]; ring
  rcases mul_eq_zero.mp h4 with h | h
  · norm_num at h
  · exact h

theorem odd_norm_two {t q a : ℤ}
    (hprim : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ 2 * a + (2 : ℕ) * t →
      ¬ (ℓ : ℤ) ^ 2 ∣ a ^ 2 + (2 : ℕ) * t * a + (2 : ℕ) ^ 2 * q) :
    Odd (a ^ 2 + (2 : ℕ) * t * a + (2 : ℕ) ^ 2 * q) := by
  have h4 := hprim 2 Nat.prime_two ⟨a + t, by push_cast; ring⟩
  push_cast at h4 ⊢
  rcases Int.even_or_odd a with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd ⟨c ^ 2 + t * c + q, by ring⟩ h4
  · exact ⟨2 * c ^ 2 + 2 * c + 2 * t * c + t + 2 * q, by ring⟩

theorem odd_of_not_two_dvd {M : ℤ} (h : ¬ ((2 : ℕ) : ℤ) ∣ M) : Odd M :=
  Int.not_even_iff_odd.mp fun h' => h (by exact_mod_cast even_iff_two_dvd.mp h')

end Arith

section Witt

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [Nontrivial k]

theorem charZero_wittVector : CharZero (WittVector p k) := by
  have hinj : Function.Injective (WittVector.map (p := p) (ZMod.castHom (dvd_refl p) k)) :=
    WittVector.map_injective _ (ZMod.castHom (dvd_refl p) k).injective
  haveI : CharZero (WittVector p (ZMod p)) :=
    (WittVector.equiv p).toRingHom.charZero
  refine ⟨fun a b hab => ?_⟩
  have h : WittVector.map (p := p) (ZMod.castHom (dvd_refl p) k) (a : WittVector p (ZMod p)) =
      WittVector.map (p := p) (ZMod.castHom (dvd_refl p) k) (b : WittVector p (ZMod p)) := by
    rw [map_natCast, map_natCast]; exact hab
  exact Nat.cast_injective (hinj h)

variable [IsDomain k]

theorem charZero_fractionRing_wittVector : CharZero (FractionRing (WittVector p k)) := by
  haveI := charZero_wittVector p k
  exact charZero_of_injective_algebraMap (IsFractionRing.injective (WittVector p k) _)

theorem charZero_algebraicClosure_fractionRing_wittVector :
    CharZero (AlgebraicClosure (FractionRing (WittVector p k))) := by
  haveI := charZero_fractionRing_wittVector p k
  exact charZero_of_injective_algebraMap
    (algebraMap (FractionRing (WittVector p k)) (AlgebraicClosure (FractionRing (WittVector p k)))).injective

end Witt

section Core

theorem charPoly_apply {G : Type*} [AddCommGroup G] {β : G →+ G} {t q : ℤ}
    (h : β.comp β + q • AddMonoidHom.id _ = t • β) (P : G) : β (β P) + q • P = t • β P := by
  have := congrArg (fun f => f P) h
  simpa using this

theorem charPoly_affine {G : Type*} [AddCommGroup G] {α₀ : G →+ G} {t q : ℤ}
    (h : α₀.comp α₀ + q • AddMonoidHom.id _ = t • α₀) (a b : ℤ) :
    (a • AddMonoidHom.id _ + b • α₀).comp (a • AddMonoidHom.id _ + b • α₀) +
        (a ^ 2 + b * t * a + b ^ 2 * q) • AddMonoidHom.id _ =
      (2 * a + b * t) • (a • AddMonoidHom.id _ + b • α₀) := by
  ext P
  have hP := charPoly_apply h P
  have hP' : α₀ (α₀ P) = t • α₀ P - q • P := by rw [← hP]; abel
  simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, map_add, map_zsmul, hP']
  module

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (ResidueField A)] [CharP (ResidueField A) p]

local notation "ℚbar" => AlgebraicClosure ℚ

theorem liftable_comb (W : WeierstrassCurve (ResidueField A)) [W.IsElliptic]
    {α₀ : W.toAffine.Point →+ W.toAffine.Point}
    (hα₀ : α₀ ∈ rationalHomSet (ResidueField A) W W)
    {t q : ℤ} (hchar : α₀.comp α₀ + q • AddMonoidHom.id _ = t • α₀) (a : ℤ) (b : ℕ)
    (hpM : ¬ (p : ℤ) ∣ a ^ 2 + (b : ℤ) * t * a + (b : ℤ) ^ 2 * q)
    (h2M : 2 ≤ a ^ 2 + (b : ℤ) * t * a + (b : ℤ) ^ 2 * q)
    (hsqM : ¬ IsSquare (a ^ 2 + (b : ℤ) * t * a + (b : ℤ) ^ 2 * q))
    (hprimM : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ 2 * a + (b : ℤ) * t →
      ¬ (ℓ : ℤ) ^ 2 ∣ a ^ 2 + (b : ℤ) * t * a + (b : ℤ) ^ 2 * q)
    (hirrM : ∀ x : ℤ, x ^ 2 - (2 * a + (b : ℤ) * t) * x + (a ^ 2 + (b : ℤ) * t * a + (b : ℤ) ^ 2 * q) ≠ 0)
    (hoddM : Odd (a ^ 2 + (b : ℤ) * t * a + (b : ℤ) ^ 2 * q)) :
    Liftable A W ((a : ℤ) • AddMonoidHom.id _ + (b : ℤ) • α₀) := by
  classical
  set M : ℤ := a ^ 2 + (b : ℤ) * t * a + (b : ℤ) ^ 2 * q with hM
  set s : ℤ := 2 * a + (b : ℤ) * t with hs
  haveI : IsAlgClosed (ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = M := ⟨M.toNat, Int.toNat_of_nonneg (by omega)⟩
  set β₀ : W.toAffine.Point →+ W.toAffine.Point := (a : ℤ) • AddMonoidHom.id _ + (b : ℤ) • α₀
    with hβ₀
  have hβ₀mem : β₀ ∈ rationalHomSet (ResidueField A) W W :=
    affine_mem_rationalHomSet (k := ResidueField A) (W := W) hα₀ a b
  have hchar' : β₀.comp β₀ + (m : ℤ) • AddMonoidHom.id _ = s • β₀ := by
    rw [hm]; exact charPoly_affine hchar a b
  have hirr' : ∀ x : ℤ, x ^ 2 - s * x + m ≠ 0 := fun x => by rw [hm]; exact hirrM x
  have hprim' : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ s → ¬ (ℓ : ℤ) ^ 2 ∣ (m : ℤ) :=
    fun ℓ hℓ hℓs => by rw [hm]; exact hprimM ℓ hℓ hℓs
  have hmk : (m : ResidueField A) ≠ 0 := by
    intro h0
    apply hpM
    have h1 : ((m : ℤ) : ResidueField A) = 0 := by exact_mod_cast h0
    rw [CharP.intCast_eq_zero_iff (ResidueField A) p] at h1
    rwa [hm] at h1
  have hodd' : Odd m := by
    have h1 : Odd (m : ℤ) := by rw [hm]; exact hoddM
    exact_mod_cast h1
  have hsq' : ¬ IsSquare m := by
    rintro ⟨r, hr⟩
    exact hsqM ⟨r, by rw [← hm, hr]; push_cast; ring⟩

  haveI : CharZero (AlgebraicClosure (FractionRing (WittVector p (ResidueField A)))) :=
    charZero_algebraicClosure_fractionRing_wittVector p (ResidueField A)
  obtain ⟨B, φ, E', hE', hΔ', hj, v', hv', β', hβ', hcompat⟩ :=
    WeierstrassCurve.exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul
      p W hβ₀mem s m hchar' hirr' hprim' hmk hodd' hsq'
      (AlgebraicClosure (FractionRing (WittVector p (ResidueField A))))
  haveI := hE'

  obtain ⟨A', e, E, hΔ, v, hv, β, hβ, hmatch⟩ :=
    WeierstrassCurve.exists_valuationSubring_variableChange_smul_eq_and_ratPointHom_reduceHom_comp_eq_of_isAlgebraic_j
      p A W β₀ B φ E' hΔ' hj v' hv' hβ' hcompat

  obtain ⟨τ, hτ, hτres⟩ :=
    ValuationSubring.exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField p A A' e
  have hres : ∀ x : A', residue A (ringEquivOfSMulEq τ hτ x) = e (residue A' x) :=
    fun x => hτres x _ rfl
  have hΔτ := twist_Δ_ne_zero τ hτ E e hres hΔ
  have hcurve := twist_map_residue τ hτ E e hres
  have hvτ : v • (twist τ hτ E).map (residue A) = W := by rw [hcurve]; exact hv
  refine ⟨twist τ hτ E, hΔτ, v, hvτ, conj τ hτ E β, conj_mem_rationalHomSet τ hτ E hβ, ?_⟩
  intro P'
  obtain ⟨P, rfl⟩ := T_surjective τ hτ E P'
  have h3 : (Affine.Point.equivOfVariableChangeEq hvτ).symm
        (reduceHom hΔτ (conj τ hτ E β (T τ hτ E P))) =
      (Affine.Point.equivOfVariableChangeEq hvτ).symm (reduceHom hΔτ (T τ hτ E (β P))) :=
    congrArg (fun Q => (Affine.Point.equivOfVariableChangeEq hvτ).symm (reduceHom hΔτ Q))
      (conj_apply_T τ hτ E β P)
  exact h3.trans ((reduce_T τ hτ E e hres v hΔ hΔτ hv hvτ (β P)).trans ((hmatch P).trans
    (congrArg β₀ (reduce_T τ hτ E e hres v hΔ hΔτ hv hvτ P).symm)))

variable {A}

theorem Liftable.congr {W : WeierstrassCurve (ResidueField A)}
    {α α' : W.toAffine.Point →+ W.toAffine.Point}
    (h : Liftable A W α) (e : α = α') : Liftable A W α' := e ▸ h

theorem Liftable.smul_of_comb {W : WeierstrassCurve (ResidueField A)}
    {α₀ : W.toAffine.Point →+ W.toAffine.Point} {a b : ℤ}
    (h : Liftable A W (a • AddMonoidHom.id _ + b • α₀)) : Liftable A W (b • α₀) := by
  refine (h.affine (-a) 1).congr ?_
  ext P
  simp only [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, one_zsmul,
    neg_zsmul]
  abel

variable (A)

theorem main (W : WeierstrassCurve (ResidueField A)) [W.IsElliptic]
    {α₀ : W.toAffine.Point →+ W.toAffine.Point}
    (hα₀ : α₀ ∈ rationalHomSet (ResidueField A) W W) (t q : ℤ)
    (hchar : α₀.comp α₀ + q • AddMonoidHom.id _ = t • α₀)
    (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0)
    (hmax : ∀ k₀ : ℤ, (p : ℤ) ∣ t - 2 * k₀ → ¬ (p : ℤ) ^ 2 ∣ k₀ ^ 2 - t * k₀ + q) :
    Liftable A W α₀ := by
  classical
  have hD := disc_ne_zero hirr
  have hp := (Fact.out : p.Prime)

  have hD2 : (((2 : ℕ) : ℤ) * t) ^ 2 - 4 * (((2 : ℕ) : ℤ) ^ 2 * q) ≠ 0 := by
    push_cast; intro h; apply hD; nlinarith
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hV : Odd t ∧ Even q
    ·
      obtain ⟨a, hpa, h2a, hsqa, hprima⟩ :=
        Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero
          (((2 : ℕ) : ℤ) * t) (((2 : ℕ) : ℤ) ^ 2 * q) hD2 2
          ⟨1, by push_cast; intro h; omega⟩
      have hL := liftable_comb 2 A W hα₀ hchar a 2 hpa h2a hsqa hprima (hirr_two hirr a)
        (odd_norm_two hprima)
      exact WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two
        A W hα₀ t q hchar hirr hV.1 hV.2 hL.smul_of_comb
    ·
      have hD1 : (((1 : ℕ) : ℤ) * t) ^ 2 - 4 * (((1 : ℕ) : ℤ) ^ 2 * q) ≠ 0 := by simpa using hD
      obtain ⟨a₀, ha₀⟩ := exists_not_two_dvd hV
      obtain ⟨a, hpa, h2a, hsqa, hprima⟩ :=
        Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero
          (((1 : ℕ) : ℤ) * t) (((1 : ℕ) : ℤ) ^ 2 * q) hD1 2 ⟨a₀, by simpa using ha₀⟩
      have hL := liftable_comb 2 A W hα₀ hchar a 1 hpa h2a hsqa hprima (hirr_one hirr a)
        (odd_of_not_two_dvd hpa)
      refine hL.smul_of_comb.congr ?_
      ext P; simp
  ·
    obtain ⟨a₀, ha₀⟩ := exists_not_dvd_of_ne_two hp hp2 (((2 : ℕ) : ℤ) * t) (((2 : ℕ) : ℤ) ^ 2 * q)
    obtain ⟨a, hpa, h2a, hsqa, hprima⟩ :=
      Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero
        (((2 : ℕ) : ℤ) * t) (((2 : ℕ) : ℤ) ^ 2 * q) hD2 p ⟨a₀, ha₀⟩
    have hL := liftable_comb p A W hα₀ hchar a 2 hpa h2a hsqa hprima (hirr_two hirr a)
      (odd_norm_two hprima)
    have h2 : (2 : ResidueField A) ≠ 0 := by
      intro h0
      have h1 : ((2 : ℕ) : ResidueField A) = 0 := by exact_mod_cast h0
      rw [CharP.cast_eq_zero_iff (ResidueField A) p] at h1
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact hp.one_lt.ne' h
      · exact hp2 h
    exact Liftable.of_two_smul h2 (by simpa using hL.smul_of_comb)

end Core

end WeierstrassCurve.DeuringLiftPlaceV2
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul.WeierstrassCurve.DeuringLiftPlaceV2"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul.WeierstrassCurve.DeuringLiftPlaceV2"

open WeierstrassCurve.DeuringLiftPlaceV2 in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p] (W : WeierstrassCurve (IsLocalRing.ResidueField A)) [W.IsElliptic] {α₀ : W.toAffine.Point →+ W.toAffine.Point} (hα₀ : α₀ ∈ WeierstrassCurve.rationalHomSet (IsLocalRing.ResidueField A) W W) (t q : ℤ) (hchar : α₀.comp α₀ + q • AddMonoidHom.id _ = t • α₀) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) (hmax : ∀ k₀ : ℤ, (p : ℤ) ∣ t - 2 * k₀ → ¬ (p : ℤ) ^ 2 ∣ k₀ ^ 2 - t * k₀ + q) : ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv : v • E.map (IsLocalRing.residue A) = W), ∃ α ∈ WeierstrassCurve.rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype), ∀ P : (E.map A.subtype).toAffine.Point, (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ (α P)) = α₀ ((WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ P)) :=
  main p A W hα₀ t q hchar hirr hmax

end S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul (solution)
