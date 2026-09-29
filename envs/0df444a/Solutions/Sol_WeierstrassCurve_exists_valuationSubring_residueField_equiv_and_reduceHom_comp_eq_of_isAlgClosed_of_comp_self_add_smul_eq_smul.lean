-- Prove2me | solution 1 for WeierstrassCurve.exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/114dac0b-8e78-5408-88da-b084b46bed5a

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
import Theorems.Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_unit_rationalHomSet_comp_eq_of_ker_le_of_comp_eq_smul_id
import Theorems.Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero
import Theorems.Thm_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom
import Theorems.Thm_WeierstrassCurve_eq_id_or_eq_neg_id_of_comp_eq_id_of_forall_two_torsion_apply_eq_self
import Theorems.Thm_WeierstrassCurve_eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_WeierstrassCurve_bijective_reduceHom_restrict_torsion
import Theorems.Thm_WeierstrassCurve_eq_of_reduceHom_eq_of_nsmul_eq_zero
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.kohelW_one Polynomial.rootESymm_zero_right WeierstrassCurve.kohelQuotient_a₂ WeierstrassCurve.kohelQuotient_a₃ WeierstrassCurve.kohelT_one WeierstrassCurve.kohelQuotient_one WeierstrassCurve.kohelQuotient_a₁ Polynomial.rootESymm_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.legendreVariableChange_s WeierstrassCurve.legendreVariableChange_t WeierstrassCurve.legendreVariableChange_r WeierstrassCurve.legendreVariableChange_u ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.deuringVariableChange_s WeierstrassCurve.deuringVariableChange_t WeierstrassCurve.deuringCurve_a₄ WeierstrassCurve.deuringCurve_a₂ WeierstrassCurve.deuringCurve_a₆ WeierstrassCurve.deuringCurve_a₁ WeierstrassCurve.deuringVariableChange_u WeierstrassCurve.deuringCurve_a₃ WeierstrassCurve.deuringVariableChange_r"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY variableChange_j a₃ a₁ map isElliptic_iff Affine.Point.some reduction map_id toAffine Affine.Point map_Δ Δ VariableChange Affine.Point.neg_some baseChange j evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet reduceHom map_residue_Δ_ne_zero_iff Affine.vcX Affine.vcY Affine.vcXInv Affine.vcYInv Affine.vcX_vcXInv Affine.vcY_vcYInv Affine.nonsingular_variableChange_iff Affine.Point.vcFun Affine.Point.vcInvFun Affine.Point.vcFun_leftInverse Affine.Point.vcFun_rightInverse Affine.Point.equivOfVariableChangeEq Affine.Point.some_congr ratPointMap_some ratPointMap_injective ratPointHom ratPointHom_apply veluQuotient veluX veluY oddOrderSummingSet Affine.Point.vcInvFun_add isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul exists_unit_rationalHomSet_comp_eq_of_ker_le_of_comp_eq_smul_id exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero reduceHom_surjective_of_henselianLocalRing exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom eq_id_or_eq_neg_id_of_comp_eq_id_of_forall_two_torsion_apply_eq_self eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self bijective_reduceHom_restrict_torsion eq_of_reduceHom_eq_of_nsmul_eq_zero comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed ReduceSurjectiveAux.isElliptic"
namespace DeuringTransport
p2m_open "WeierstrassCurve"

section FieldIso

variable {k κ : Type} [Field k] [Field κ] [DecidableEq k] [DecidableEq κ]
variable (φ : k ≃+* κ) (W : WeierstrassCurve k)

theorem ratPointHom_bijective :
    Function.Bijective (WeierstrassCurve.ratPointHom φ.toRingHom (W₀ := W)) := by
  refine ⟨fun P Q h => WeierstrassCurve.ratPointMap_injective φ.toRingHom h, ?_⟩
  rintro (_ | ⟨x', y', h'⟩)
  · exact ⟨0, rfl⟩
  · have hns : W.toAffine.Nonsingular (φ.symm x') (φ.symm y') := by
      rw [← W.toAffine.map_nonsingular φ.toRingHom.injective]
      simpa using h'
    refine ⟨.some _ _ hns, ?_⟩
    rw [WeierstrassCurve.ratPointHom_apply, WeierstrassCurve.ratPointMap_some]
    exact WeierstrassCurve.Affine.Point.some_congr (by simp) (by simp) _ _

noncomputable def mapEquiv : W.toAffine.Point ≃+ (W.map φ.toRingHom).toAffine.Point :=
  AddEquiv.ofBijective (WeierstrassCurve.ratPointHom φ.toRingHom) (ratPointHom_bijective φ W)

theorem mapEquiv_apply (P : W.toAffine.Point) :
    mapEquiv φ W P = WeierstrassCurve.ratPointHom φ.toRingHom P := rfl

theorem mapEquiv_some {x y : k} (h : W.toAffine.Nonsingular x y) :
    mapEquiv φ W (.some x y h) = .some (φ x) (φ y)
      ((W.toAffine.map_nonsingular φ.toRingHom.injective x y).mpr h) := rfl

theorem mapEquiv_symm_some {x' y' : κ} (h' : (W.map φ.toRingHom).toAffine.Nonsingular x' y') :
    ∃ h, (mapEquiv φ W).symm (.some x' y' h') = .some (φ.symm x') (φ.symm y') h := by
  have hns : W.toAffine.Nonsingular (φ.symm x') (φ.symm y') := by
    rw [← W.toAffine.map_nonsingular φ.toRingHom.injective]
    simpa using h'
  refine ⟨hns, ?_⟩
  apply (mapEquiv φ W).injective
  rw [AddEquiv.apply_symm_apply, mapEquiv_some]
  exact WeierstrassCurve.Affine.Point.some_congr (by simp) (by simp) _ _

theorem evalEvalBC_self {F : Type*} [Field F] (p : F[X][Y]) (x y : F) :
    WeierstrassCurve.evalEvalBC F p x y = p.evalEval x y := by
  simp only [WeierstrassCurve.evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id,
    Polynomial.map_id]

theorem conj_mapEquiv_mem_rationalHomSet {α : W.toAffine.Point →+ W.toAffine.Point}
    (hα : α ∈ rationalHomSet k W W) :
    ((mapEquiv φ W).toAddMonoidHom.comp (α.comp (mapEquiv φ W).symm.toAddMonoidHom)) ∈
      rationalHomSet κ (W.map φ.toRingHom) (W.map φ.toRingHom) := by
  rcases hα with h0 | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · left
    subst h0
    ext P
    change mapEquiv φ W ((0 : W.toAffine.Point →+ W.toAffine.Point) ((mapEquiv φ W).symm P)) = 0
    rw [AddMonoidHom.zero_apply, map_zero]
  · right
    refine ⟨nX.map (mapRingHom φ.toRingHom), dX.map (mapRingHom φ.toRingHom),
      nY.map (mapRingHom φ.toRingHom), dY.map (mapRingHom φ.toRingHom), φ '' B, hB.image _, ?_⟩
    intro x' y' h' hx'
    obtain ⟨h, hsymm⟩ := mapEquiv_symm_some φ W h'
    have hxB : φ.symm x' ∉ B := fun hmem => hx' ⟨_, hmem, by simp⟩
    obtain ⟨hdX, hdY, h'', hα'⟩ := hrep (φ.symm x') (φ.symm y') h hxB
    have hev : ∀ q : k[X][Y], WeierstrassCurve.evalEvalBC κ (q.map (mapRingHom φ.toRingHom)) x' y' =
        φ (WeierstrassCurve.evalEvalBC k q (φ.symm x') (φ.symm y')) := by
      intro q
      rw [evalEvalBC_self, evalEvalBC_self]
      conv_lhs => rw [show x' = φ.toRingHom (φ.symm x') by simp, show y' = φ.toRingHom (φ.symm y') by simp]
      rw [Polynomial.map_mapRingHom_evalEval]
      rfl
    refine ⟨by rw [hev]; exact (map_ne_zero φ).mpr hdX, by rw [hev]; exact (map_ne_zero φ).mpr hdY, ?_⟩
    have key : ((mapEquiv φ W).toAddMonoidHom.comp (α.comp (mapEquiv φ W).symm.toAddMonoidHom))
        (.some x' y' h') = .some (φ (WeierstrassCurve.evalEvalBC k nX (φ.symm x') (φ.symm y') /
            WeierstrassCurve.evalEvalBC k dX (φ.symm x') (φ.symm y')))
          (φ (WeierstrassCurve.evalEvalBC k nY (φ.symm x') (φ.symm y') /
            WeierstrassCurve.evalEvalBC k dY (φ.symm x') (φ.symm y')))
          ((W.toAffine.map_nonsingular φ.toRingHom.injective _ _).mpr h'') := by
      have hα'' : α (.some (φ.symm x') (φ.symm y') h) =
          .some (WeierstrassCurve.evalEvalBC k nX (φ.symm x') (φ.symm y') /
              WeierstrassCurve.evalEvalBC k dX (φ.symm x') (φ.symm y'))
            (WeierstrassCurve.evalEvalBC k nY (φ.symm x') (φ.symm y') /
              WeierstrassCurve.evalEvalBC k dY (φ.symm x') (φ.symm y')) h'' := hα'
      change mapEquiv φ W (α ((mapEquiv φ W).symm (.some x' y' h'))) = _
      rw [hsymm, hα'', mapEquiv_some]
    have hsome : ∀ {x₁ y₁ x₂ y₂ : κ} (h₁ : (W.map φ.toRingHom).toAffine.Nonsingular x₁ y₁),
        x₁ = x₂ → y₁ = y₂ → ∃ h₂, (Affine.Point.some x₁ y₁ h₁ : (W.map φ.toRingHom).toAffine.Point)
          = Affine.Point.some x₂ y₂ h₂ := by
      intro x₁ y₁ x₂ y₂ h₁ hx hy
      subst hx hy
      exact ⟨h₁, rfl⟩
    have hx₂ : φ (WeierstrassCurve.evalEvalBC k nX (φ.symm x') (φ.symm y') /
        WeierstrassCurve.evalEvalBC k dX (φ.symm x') (φ.symm y')) =
        WeierstrassCurve.evalEvalBC κ (nX.map (mapRingHom φ.toRingHom)) x' y' /
          WeierstrassCurve.evalEvalBC κ (dX.map (mapRingHom φ.toRingHom)) x' y' := by
      rw [map_div₀, hev, hev]
    have hy₂ : φ (WeierstrassCurve.evalEvalBC k nY (φ.symm x') (φ.symm y') /
        WeierstrassCurve.evalEvalBC k dY (φ.symm x') (φ.symm y')) =
        WeierstrassCurve.evalEvalBC κ (nY.map (mapRingHom φ.toRingHom)) x' y' /
          WeierstrassCurve.evalEvalBC κ (dY.map (mapRingHom φ.toRingHom)) x' y' := by
      rw [map_div₀, hev, hev]
    obtain ⟨h₂, e₂⟩ := hsome ((W.toAffine.map_nonsingular φ.toRingHom.injective _ _).mpr h'') hx₂ hy₂
    exact ⟨h₂, key.trans e₂⟩

end FieldIso

section VC

variable {K : Type*} [Field K] [DecidableEq K]

theorem some_congr' {V : Affine K} {x₁ y₁ x₂ y₂ : K} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem some_eq_some' {V : Affine K} {x y x' y' : K} (h : V.Nonsingular x y) (hx : x = x')
    (hy : y = y') : ∃ h', Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  subst hx hy
  exact ⟨h, rfl⟩

theorem vcFun_add (γ : VariableChange K) (W : Affine K) (P Q : (γ • W).toAffine.Point) :
    Affine.Point.vcFun γ W (P + Q) = Affine.Point.vcFun γ W P + Affine.Point.vcFun γ W Q := by
  have hl : Function.LeftInverse (Affine.Point.vcInvFun γ W) (Affine.Point.vcFun γ W) :=
    Affine.Point.vcFun_leftInverse
  have hr : Function.RightInverse (Affine.Point.vcInvFun γ W) (Affine.Point.vcFun γ W) :=
    Affine.Point.vcFun_rightInverse
  have := Affine.Point.vcInvFun_add γ W (Affine.Point.vcFun γ W P) (Affine.Point.vcFun γ W Q)
  rw [hl P, hl Q] at this
  rw [← hr (Affine.Point.vcFun γ W P + Affine.Point.vcFun γ W Q), this]

variable {γ : VariableChange K} {W V : WeierstrassCurve K}

theorem equivOfVariableChangeEq_zero (h : γ • W = V) :
    Affine.Point.equivOfVariableChangeEq h 0 = 0 := by
  subst h; rfl

theorem equivOfVariableChangeEq_some (h : γ • W = V) {x y : K} (hxy : V.toAffine.Nonsingular x y) :
    Affine.Point.equivOfVariableChangeEq h (.some x y hxy) =
      .some (Affine.vcX γ x) (Affine.vcY γ x y)
        ((Affine.nonsingular_variableChange_iff x y).mp (h ▸ hxy)) := by
  subst h; rfl

theorem equivOfVariableChangeEq_add (h : γ • W = V) (P Q : V.toAffine.Point) :
    Affine.Point.equivOfVariableChangeEq h (P + Q) =
      Affine.Point.equivOfVariableChangeEq h P + Affine.Point.equivOfVariableChangeEq h Q := by
  subst h
  exact vcFun_add γ W P Q

noncomputable def vcAddEquiv (h : γ • W = V) : V.toAffine.Point ≃+ W.toAffine.Point :=
  { Affine.Point.equivOfVariableChangeEq h with map_add' := equivOfVariableChangeEq_add h }

theorem vcAddEquiv_apply (h : γ • W = V) (P : V.toAffine.Point) :
    vcAddEquiv h P = Affine.Point.equivOfVariableChangeEq h P := rfl

theorem vcAddEquiv_symm_apply (h : γ • W = V) (P : W.toAffine.Point) :
    (vcAddEquiv h).symm P = (Affine.Point.equivOfVariableChangeEq h).symm P := rfl

theorem vcAddEquiv_symm_some (h : γ • W = V) {x y : K} (hxy : W.toAffine.Nonsingular x y) :
    ∃ h', (vcAddEquiv h).symm (.some x y hxy) =
      .some (Affine.vcXInv γ x) (Affine.vcYInv γ x y) h' := by
  have hns : V.toAffine.Nonsingular (Affine.vcXInv γ x) (Affine.vcYInv γ x y) := by
    subst h
    exact (Affine.nonsingular_variableChange_iff _ _).mpr (by rwa [Affine.vcX_vcXInv, Affine.vcY_vcYInv])
  refine ⟨hns, ?_⟩
  apply (vcAddEquiv h).injective
  rw [AddEquiv.apply_symm_apply, vcAddEquiv_apply, equivOfVariableChangeEq_some]
  exact some_congr' (Affine.vcX_vcXInv x).symm (Affine.vcY_vcYInv x y).symm _ _

theorem evalEvalBC_self' (p : K[X][Y]) (x y : K) :
    WeierstrassCurve.evalEvalBC K p x y = p.evalEval x y := by
  simp only [WeierstrassCurve.evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id,
    Polynomial.map_id]

theorem vcAddEquiv_mem_rationalHomSet (h : γ • W = V) :
    ((vcAddEquiv h).toAddMonoidHom : (V.baseChange K).toAffine.Point →+ (W.baseChange K).toAffine.Point)
      ∈ rationalHomSet K V W := by
  right
  refine ⟨C (C γ.r + C ((γ.u : K) ^ 2) * X), 1,
    C (C γ.t + C ((γ.u : K) ^ 2 * γ.s) * X) + C (C ((γ.u : K) ^ 3)) * Y, 1, ∅, Set.finite_empty, ?_⟩
  intro x y hxy _
  simp only [evalEvalBC_self', evalEval_one, evalEval_C, evalEval_add, evalEval_mul, evalEval_X,
    eval_add, eval_mul, eval_C, eval_X, ne_eq, one_ne_zero, not_false_eq_true, div_one, true_and]
  obtain ⟨h', e'⟩ := some_eq_some' ((Affine.nonsingular_variableChange_iff x y).mp (h ▸ hxy))
    (show Affine.vcX γ x = γ.r + (γ.u : K) ^ 2 * x by simp only [Affine.vcX]; ring)
    (show Affine.vcY γ x y = γ.t + (γ.u : K) ^ 2 * γ.s * x + (γ.u : K) ^ 3 * y by
      simp only [Affine.vcY]; ring)
  exact ⟨h', (equivOfVariableChangeEq_some h hxy).trans e'⟩

theorem vcAddEquiv_symm_mem_rationalHomSet (h : γ • W = V) :
    ((vcAddEquiv h).symm.toAddMonoidHom :
      (W.baseChange K).toAffine.Point →+ (V.baseChange K).toAffine.Point) ∈ rationalHomSet K W V := by
  right
  refine ⟨C (C (((γ.u⁻¹ : Kˣ) : K) ^ 2) * (X - C γ.r)), 1,
    C (C (((γ.u⁻¹ : Kˣ) : K) ^ 3)) * (Y - C (C γ.t) - C (C γ.s * (X - C γ.r))), 1, ∅,
    Set.finite_empty, ?_⟩
  intro x y hxy _
  simp only [evalEvalBC_self', evalEval_one, evalEval_C, evalEval_sub, evalEval_mul, evalEval_X,
    eval_sub, eval_mul, eval_C, eval_X, ne_eq, one_ne_zero, not_false_eq_true, div_one, true_and]
  obtain ⟨h', e⟩ := vcAddEquiv_symm_some h hxy
  obtain ⟨h'', e'⟩ := some_eq_some' h'
    (show Affine.vcXInv γ x = ((γ.u⁻¹ : Kˣ) : K) ^ 2 * (x - γ.r) by simp only [Affine.vcXInv])
    (show Affine.vcYInv γ x y = ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (y - γ.t - γ.s * (x - γ.r)) by
      simp only [Affine.vcYInv])
  exact ⟨h'', e.trans e'⟩

end VC

section Conj

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def conj (e : A ≃+ B) (β : A →+ A) : B →+ B :=
  e.toAddMonoidHom.comp (β.comp e.symm.toAddMonoidHom)

theorem conj_apply (e : A ≃+ B) (β : A →+ A) (b : B) : conj e β b = e (β (e.symm b)) := rfl

theorem conj_apply_apply (e : A ≃+ B) (β : A →+ A) (a : A) : conj e β (e a) = e (β a) := by
  rw [conj_apply, AddEquiv.symm_apply_apply]

theorem conj_charPoly (e : A ≃+ B) {β : A →+ A} {s m : ℤ}
    (h : β.comp β + m • AddMonoidHom.id _ = s • β) :
    (conj e β).comp (conj e β) + m • AddMonoidHom.id _ = s • conj e β := by
  ext b
  have := DFunLike.congr_fun h (e.symm b)
  simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.smul_apply, AddMonoidHom.id_apply] at this
  simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.smul_apply, AddMonoidHom.id_apply, conj_apply, AddEquiv.symm_apply_apply]
  rw [← e.apply_symm_apply b]
  conv_lhs => rw [AddEquiv.symm_apply_apply, ← map_zsmul, ← map_add, this, map_zsmul]
  rw [AddEquiv.symm_apply_apply]

theorem mem_ker_conj_iff (e : A ≃+ B) (β : A →+ A) (b : B) :
    b ∈ (conj e β).ker ↔ e.symm b ∈ β.ker := by
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, conj_apply, map_eq_zero_iff _ e.injective]

theorem conj_trans (e : A ≃+ B) {C' : Type*} [AddCommGroup C'] (f : B ≃+ C') (β : A →+ A) :
    conj (e.trans f) β = conj f (conj e β) := by
  ext c; rfl

end Conj

end WeierstrassCurve.DeuringTransport

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY variableChange_j a₃ a₁ map isElliptic_iff Affine.Point.some reduction map_id toAffine Affine.Point map_Δ Δ VariableChange Affine.Point.neg_some baseChange j evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet reduceHom map_residue_Δ_ne_zero_iff Affine.vcX Affine.vcY Affine.vcXInv Affine.vcYInv Affine.vcX_vcXInv Affine.vcY_vcYInv Affine.nonsingular_variableChange_iff Affine.Point.vcFun Affine.Point.vcInvFun Affine.Point.vcFun_leftInverse Affine.Point.vcFun_rightInverse Affine.Point.equivOfVariableChangeEq Affine.Point.some_congr ratPointMap_some ratPointMap_injective ratPointHom ratPointHom_apply veluQuotient veluX veluY oddOrderSummingSet Affine.Point.vcInvFun_add isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul exists_unit_rationalHomSet_comp_eq_of_ker_le_of_comp_eq_smul_id exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero reduceHom_surjective_of_henselianLocalRing exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom eq_id_or_eq_neg_id_of_comp_eq_id_of_forall_two_torsion_apply_eq_self eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self bijective_reduceHom_restrict_torsion eq_of_reduceHom_eq_of_nsmul_eq_zero comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed ReduceSurjectiveAux.isElliptic"
namespace DeuringLocal
p2m_open "WeierstrassCurve"

open IsLocalRing DeuringTransport

theorem exists_torsion_lift {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    [HenselianLocalRing A] [DecidableEq (ResidueField A)] [IsAlgClosed (ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ}
    (hN : (N : ResidueField A) ≠ 0) (Q : (W.map (residue A)).toAffine.Point) (hQ : N • Q = 0) :
    ∃ P : (W.map A.subtype).toAffine.Point, N • P = 0 ∧ WeierstrassCurve.reduceHom hΔ P = Q := by
  obtain ⟨⟨P, hP⟩, h⟩ := (WeierstrassCurve.bijective_reduceHom_restrict_torsion hΔ hN).2 ⟨Q, hQ⟩
  exact ⟨P, hP, congrArg Subtype.val h⟩

theorem card_range_torsion {E V : Type*} [AddCommGroup E] [AddCommGroup V] (φ : E →+ V) {m : ℕ}
    (hm : m ≠ 0) (Q : E) (hQ : addOrderOf Q = m) (hker : φ.ker = AddSubgroup.zmultiples Q)
    (hcard : Nat.card (Submodule.torsionBy ℤ E (m : ℤ)) = m ^ 2) :
    Nat.card (φ.comp (Submodule.torsionBy ℤ E (m : ℤ)).toAddSubgroup.subtype).range = m := by
  set T := (Submodule.torsionBy ℤ E (m : ℤ)).toAddSubgroup with hT
  have hTcard : Nat.card T = m ^ 2 := hcard
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hTcard]; exact pow_ne_zero 2 hm)
  let g : T →+ V := φ.comp T.subtype
  have hg : ∀ P : T, g P = φ (P : E) := fun P => rfl
  have h1 : Nat.card T = Nat.card (T ⧸ g.ker) * Nat.card g.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have hq : Nat.card (T ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv
  have hQT : Q ∈ T := by
    rw [hT, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
    change (m : ℤ) • Q = 0
    rw [natCast_zsmul, ← hQ, addOrderOf_nsmul_eq_zero]
  have hgker : Nat.card g.ker = m := by
    have e : Nat.card g.ker = Nat.card (AddSubgroup.zmultiples Q) := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun P => (⟨((P : T) : E), by
          have h0 : φ ((P : T) : E) = 0 := (AddMonoidHom.mem_ker).mp P.2
          rw [← hker]; exact h0⟩ : AddSubgroup.zmultiples Q)) ⟨?_, ?_⟩)
      · intro P₁ P₂ h12
        have h := congrArg Subtype.val h12
        exact Subtype.ext (Subtype.ext h)
      · rintro ⟨R, hR⟩
        have hRT : R ∈ T := by
          obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
          exact T.zsmul_mem hQT j
        have hRker : φ R = 0 := by rw [← AddMonoidHom.mem_ker, hker]; exact hR
        exact ⟨⟨⟨R, hRT⟩, (AddMonoidHom.mem_ker).mpr hRker⟩, rfl⟩
    rw [e, Nat.card_zmultiples, hQ]
  have key : m ^ 2 = Nat.card g.range * m := by rw [← hTcard, h1, hq, hgker]
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm
  rw [sq] at key
  exact (Nat.eq_of_mul_eq_mul_right hm0 key).symm

theorem j_eq_of_eq {R : Type*} [CommRing R] {E₁ E₂ : WeierstrassCurve R} [E₁.IsElliptic]
    [E₂.IsElliptic] (h : E₁ = E₂) : E₁.j = E₂.j := by
  subst h; rfl

theorem eval_map_self_eq_eval₂_diag {R : Type*} [CommRing R] (Φ : Polynomial (Polynomial ℤ)) (x : R) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)).eval x
      = (Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).eval₂ (Int.castRingHom R) x := by
  rw [Polynomial.eval_map]
  have h := Polynomial.hom_eval₂ Φ (RingHom.id (Polynomial ℤ))
    (Polynomial.eval₂RingHom (Int.castRingHom R) x) Polynomial.X
  rw [Polynomial.coe_eval₂RingHom] at h
  rw [h, RingHom.comp_id, Polynomial.eval₂_X]

theorem isAlgebraic_j_of_smul_eq_veluQuotient {Ω : Type*} [Field Ω] [DecidableEq Ω] [IsAlgClosed Ω]
    [CharZero Ω] (E : WeierstrassCurve Ω) [E.IsElliptic] (n : ℕ) (hsq : ¬ IsSquare (2 * n + 1))
    (Q : E.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) (γ : VariableChange Ω)
    (hγ : γ • E = E.veluQuotient (E.oddOrderSummingSet Q n)) : IsAlgebraic ℚ E.j := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData (2 * n + 1)
  have hΔq : (E.veluQuotient (E.oddOrderSummingSet Q n)).Δ ≠ 0 :=
    veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq E n Q hQ
  haveI hell : (E.veluQuotient (E.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔq⟩
  have hroot := ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq_of_isAlgClosed
    E n Q hQ hΔq data
  have hjq : (E.veluQuotient (E.oddOrderSummingSet Q n)).j = E.j :=
    (j_eq_of_eq hγ.symm).trans (E.variableChange_j γ)
  set D : Polynomial ℤ := data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X with hDdef
  have hD : IsUnit D.leadingCoeff :=
    ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare (2 * n + 1) hsq data
  have hD0 : D ≠ 0 := by
    intro h0; rw [h0, Polynomial.leadingCoeff_zero] at hD; exact not_isUnit_zero hD
  have hev : D.eval₂ (Int.castRingHom Ω) E.j = 0 := by
    rw [← eval_map_self_eq_eval₂_diag]
    have := hroot
    rw [Polynomial.IsRoot.def] at this
    convert this using 2
    exact hjq.symm
  refine ⟨D.map (Int.castRingHom ℚ), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (Int.castRingHom ℚ).injective_int).mpr hD0
  · have h1 : Polynomial.aeval E.j (D.map (Int.castRingHom ℚ)) = Polynomial.aeval E.j D := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from RingHom.ext_int _ _, Polynomial.aeval_map_algebraMap]
    rw [h1, Polynomial.aeval_def, show algebraMap ℤ Ω = Int.castRingHom Ω from RingHom.ext_int _ _]
    exact hev

open scoped Classical in

theorem exists_marked_lift
    (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (hsq : ¬ IsSquare (2 * n + 1)) (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1)
    (γ₀ : WeierstrassCurve.VariableChange k)
    (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra (FractionRing (WittVector p k)) Ω]
    [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] :
    ∃ ℓ : ℕ, (ℓ = 2 ∨ ℓ = 3) ∧ (ℓ : k) ≠ 0 ∧
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
        (ℓ : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
          ∈ AddSubgroup.zmultiples Q₀ →
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        (ℓ : ℤ) • (WeierstrassCurve.Affine.Point.some x' y' h' : (E'.map B.subtype).toAffine.Point)
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
  by_cases h2 : (2 : k) = 0
  · have h3 : (3 : k) ≠ 0 := by
      intro h3
      have : (1 : k) = 0 := by linear_combination h3 - h2
      exact one_ne_zero this
    obtain ⟨B, φ, E', hE', hΔ', v', hv', Q', hQ', hQ'red, γ, hγ, H⟩ :=
      W.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_three_smul_mem_zmultiples_of_two_eq_zero
        p h2 n hm hsq Q₀ hQ₀ γ₀ hγ₀ Ω
    refine ⟨3, Or.inr rfl, h3, B, φ, E', hE', hΔ', v', hv', Q', hQ', hQ'red, γ, hγ, ?_⟩
    intro x' y' h' x y h hx1 hx2 hx3 hred
    exact H x' y' h' x y h (by simpa using hx1) hx2 (by simpa using hx3) hred
  · obtain ⟨B, φ, E', hE', hΔ', v', hv', Q', hQ', hQ'red, γ, hγ, H⟩ :=
      W.exists_valuationSubring_lift_variableChange_veluQuotient_reduceHom_eq_of_two_smul_mem_zmultiples
        p h2 n hm hsq Q₀ hQ₀ γ₀ hγ₀ Ω
    refine ⟨2, Or.inl rfl, h2, B, φ, E', hE', hΔ', v', hv', Q', hQ', hQ'red, γ, hγ, ?_⟩
    intro x' y' h' x y h hx1 hx2 hx3 hred
    exact H x' y' h' x y h (by simpa using hx1) hx2 (by simpa using hx3) hred

private theorem _root_.WeierstrassCurve.ReduceSurjectiveAux.isElliptic {L : Type*} [Field L]
    {A : ValuationSubring L} {W : WeierstrassCurve A}
    (hΔ : (W.map (IsLocalRing.residue A)).Δ ≠ 0) : (W.map A.subtype).IsElliptic := by
  have hu : IsUnit W.Δ := (map_residue_Δ_ne_zero_iff W).mp hΔ
  rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
  exact hu.map A.subtype

p2m_alias "P2MW.S_WeierstrassCurve_exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul.WeierstrassCurve.ReduceSurjectiveAux.isElliptic" "WeierstrassCurve.ReduceSurjectiveAux.isElliptic"

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

end HomSet

section NonTorsion

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

omit [IsAlgClosed k] [DecidableEq k] in
theorem natCast_ne_zero_of_prime_of_lt {ℓ : ℕ} (hℓ : ℓ.Prime) (hlt : ringChar k < ℓ) :
    (ℓ : k) ≠ 0 := by
  intro h
  have hdvd : ringChar k ∣ ℓ := (ringChar.spec k ℓ).mp h
  rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

theorem finite_torsionBy {n : ℕ} (hn : (n : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point n) := by
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  exact Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn0)

theorem exists_zsmul_ne_zero {M : ℤ} (hM : M ≠ 0) : ∃ P : W.toAffine.Point, M • P ≠ 0 := by
  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (M.natAbs + ringChar k + 1)
  have hℓM : ¬ (ℓ : ℤ) ∣ M := by
    intro h
    have h1 : ℓ ≤ M.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hM) (Int.natCast_dvd.mp h)
    omega
  have hℓk : (ℓ : k) ≠ 0 := natCast_ne_zero_of_prime_of_lt hℓ (by omega)
  have hcard : Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed W hℓk
  have hgt : 1 < Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) := by
    rw [hcard]; nlinarith [hℓ.one_lt]
  haveI : Finite (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) := finite_torsionBy W hℓk
  haveI : Nontrivial (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) :=
    Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨⟨P, hP⟩, hP0⟩ := exists_ne (0 : Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ)
  have hPℓ : (ℓ : ℤ) • P = 0 := by simpa using hP
  have hP0' : P ≠ 0 := fun h => hP0 (by ext; simpa using h)
  refine ⟨P, fun hMP => hP0' ?_⟩
  have hcop : IsCoprime (ℓ : ℤ) M := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd (ℓ : ℤ) M ∣ ℓ := by
      have := Int.gcd_dvd_left (ℓ : ℤ) M
      exact_mod_cast this
    rcases (Nat.dvd_prime hℓ).mp h1 with h | h
    · exact h
    · exfalso
      apply hℓM
      have := Int.gcd_dvd_right (ℓ : ℤ) M
      rwa [h] at this
  obtain ⟨a, b, hab⟩ := hcop
  have hMP' : M • P = 0 := hMP
  calc P = (a * ℓ + b * M) • P := by rw [hab, one_zsmul]
    _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, hPℓ, hMP', zsmul_zero, zsmul_zero, add_zero]

theorem exists_zsmul_eq {M : ℤ} (hM : M ≠ 0) (P : W.toAffine.Point) :
    ∃ P' : W.toAffine.Point, M • P' = P := by
  have hmem : (M • AddMonoidHom.id _ : (W.baseChange k).toAffine.Point →+ _) ∈ rationalHomSet k W W :=
    zsmul_id_mem_rationalHomSet W M
  have hne : (M • AddMonoidHom.id _ : (W.baseChange k).toAffine.Point →+ _) ≠ 0 := by
    intro h0
    obtain ⟨R, hR⟩ := exists_zsmul_ne_zero W hM
    exact hR (by first | simpa using DFunLike.congr_fun h0 R | (have h := DFunLike.congr_fun h0 R; simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at h; exact h) | exact DFunLike.congr_fun h0 R)
  obtain ⟨P', hP'⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hmem hne P
  exact ⟨P', by first | simpa using hP' | exact hP'⟩

theorem eq_zero_of_zsmul_apply_eq_zero {G : Type*} [AddCommGroup G] {M : ℤ} (hM : M ≠ 0)
    (δ : W.toAffine.Point →+ G) (h : ∀ P, M • δ P = 0) : δ = 0 := by
  ext P
  obtain ⟨P', rfl⟩ := exists_zsmul_eq W hM P
  rw [map_zsmul, h P', AddMonoidHom.zero_apply]

theorem charPoly_apply {G : Type*} [AddCommGroup G] {β : G →+ G} {s m : ℤ}
    (h : β.comp β + m • AddMonoidHom.id _ = s • β) (P : G) : β (β P) + m • P = s • β P := by
  have := DFunLike.congr_fun h P
  simpa using this

theorem comp_conj_apply {G : Type*} [AddCommGroup G] {β : G →+ G} {s m : ℤ}
    (hchar : β.comp β + m • AddMonoidHom.id _ = s • β) (P : G) :
    β ((s • AddMonoidHom.id G - β) P) = m • P := by
  have e1 := charPoly_apply hchar P
  have e3 : β (β P) = s • β P - m • P := eq_sub_of_add_eq e1
  have e4 : (s • AddMonoidHom.id G - β) P = s • P - β P := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
  rw [e4, map_sub, map_zsmul, e3]
  module

end NonTorsion

open scoped Classical in
theorem main (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
    [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    {β₀ : W.toAffine.Point →+ W.toAffine.Point} (hβ₀ : β₀ ∈ WeierstrassCurve.rationalHomSet k W W)
    (s : ℤ) (m : ℕ) (hchar : β₀.comp β₀ + (m : ℤ) • AddMonoidHom.id _ = s • β₀)
    (hirr : ∀ x : ℤ, x ^ 2 - s * x + m ≠ 0)
    (hprim : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ s → ¬ (ℓ : ℤ) ^ 2 ∣ (m : ℤ)) (hm : (m : k) ≠ 0)
    (hodd : Odd m) (hsq : ¬ IsSquare m) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra (FractionRing (WittVector p k)) Ω] [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] :
    ∃ (B : ValuationSubring Ω) (φ : k ≃+* IsLocalRing.ResidueField B) (E' : WeierstrassCurve B)
      (_ : E'.IsElliptic) (hΔ' : (E'.map (IsLocalRing.residue B)).Δ ≠ 0)
      (_ : IsAlgebraic ℚ (E'.map B.subtype).j)
      (v' : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B))
      (hv' : v' • E'.map (IsLocalRing.residue B) = W.map φ.toRingHom),
      ∃ β' ∈ WeierstrassCurve.rationalHomSet Ω (E'.map B.subtype) (E'.map B.subtype),
        ∀ (Q : (E'.map B.subtype).toAffine.Point) (P₀ : W.toAffine.Point),
          WeierstrassCurve.ratPointHom φ.toRingHom P₀ =
            (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
              (WeierstrassCurve.reduceHom hΔ' Q) →
          WeierstrassCurve.ratPointHom φ.toRingHom (β₀ P₀) =
            (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
              (WeierstrassCurve.reduceHom hΔ' (β' Q)) := by
  classical

  obtain ⟨n, hn⟩ := hodd
  have hmn : m = 2 * n + 1 := hn
  have hn0 : m ≠ 0 := by omega
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hn0
  have hmk : ((2 * n + 1 : ℕ) : k) ≠ 0 := by rw [← hmn]; exact hm
  have hsq' : ¬ IsSquare (2 * n + 1) := by rw [← hmn]; exact hsq

  obtain ⟨hcyc, hcardβ⟩ :=
    W.isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul hβ₀ s m hchar hm hirr hprim
  haveI hfinβ : Finite β₀.ker := Nat.finite_of_card_ne_zero (by rw [hcardβ]; exact hn0)
  obtain ⟨⟨Q₀, hQ₀ker⟩, hg⟩ := hcyc.exists_generator
  have hordg : addOrderOf (⟨Q₀, hQ₀ker⟩ : β₀.ker) = m :=
    (addOrderOf_eq_card_of_forall_mem_zmultiples hg).trans hcardβ
  have hordQ₀ : addOrderOf Q₀ = m := by
    rw [← hordg]
    exact (AddSubgroup.addOrderOf_mk (H := β₀.ker) Q₀ hQ₀ker).symm
  have hkerβ : β₀.ker = AddSubgroup.zmultiples Q₀ := by
    apply le_antisymm
    · intro P hP
      obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨P, hP⟩)
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨j, ?_⟩
      have := congrArg Subtype.val hj
      simpa using this
    · exact AddSubgroup.zmultiples_le.mpr hQ₀ker
  have hQ₀ : addOrderOf Q₀ = 2 * n + 1 := hordQ₀.trans hmn
  have hQ₀β : β₀ Q₀ = 0 := (AddMonoidHom.mem_ker).mp hQ₀ker

  obtain ⟨φb, hφbker, hφb⟩ :=
    W.exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one n hmk Q₀ hQ₀
  have hchar' : β₀.comp β₀ + ((2 * n + 1 : ℕ) : ℤ) • AddMonoidHom.id _ = s • β₀ := by rw [← hmn]; exact hchar
  have hirr' : ∀ x : ℤ, x ^ 2 - s * x + (2 * n + 1 : ℕ) ≠ 0 := by rw [← hmn]; exact hirr
  have hprim' : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ s → ¬ (ℓ : ℤ) ^ 2 ∣ ((2 * n + 1 : ℕ) : ℤ) := by
    rw [← hmn]; exact hprim
  obtain ⟨γ₀, hγ₀, hβ₀fac⟩ :=
    W.exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul
      hβ₀ s n hchar' hirr' hprim' hmk Q₀ hQ₀ hQ₀β φb hφbker hφb

  obtain ⟨ℓ, hℓ23, hℓk, B, φ, E', hE', hΔ', v', hv', Q', hQ', hQ'red, γ, hγ, HMS⟩ :=
    exists_marked_lift p W n hmk hsq' Q₀ hQ₀ γ₀ hγ₀ Ω

  haveI : E'.IsElliptic := hE'
  haveI hBhens : HenselianLocalRing B := ValuationSubring.henselianLocalRing_of_isAlgClosed B
  haveI hκac : IsAlgClosed (IsLocalRing.ResidueField B) := ValuationSubring.isAlgClosed_residueField B
  haveI hEΩ : (E'.map B.subtype).IsElliptic :=
    WeierstrassCurve.ReduceSurjectiveAux.isElliptic hΔ'
  have hmκ : (m : IsLocalRing.ResidueField B) ≠ 0 := by
    rw [← map_natCast φ.toRingHom m]; exact (map_ne_zero φ.toRingHom).mpr hm
  have hℓκ : (ℓ : IsLocalRing.ResidueField B) ≠ 0 := by
    rw [← map_natCast φ.toRingHom ℓ]; exact (map_ne_zero φ.toRingHom).mpr hℓk
  have hmΩ : ((2 * n + 1 : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmΩ' : (m : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn0

  let e₁ : (W.map φ.toRingHom).toAffine.Point ≃+ (E'.map (IsLocalRing.residue B)).toAffine.Point :=
    vcAddEquiv hv'
  let Tr : W.toAffine.Point ≃+ (E'.map (IsLocalRing.residue B)).toAffine.Point :=
    (mapEquiv φ W).trans e₁
  let βt : (E'.map (IsLocalRing.residue B)).toAffine.Point →+
      (E'.map (IsLocalRing.residue B)).toAffine.Point := conj Tr β₀
  have hβt_apply : ∀ P, βt (Tr P) = Tr (β₀ P) := fun P => conj_apply_apply Tr β₀ P
  have hβtrat : βt ∈ rationalHomSet (IsLocalRing.ResidueField B) (E'.map (IsLocalRing.residue B))
      (E'.map (IsLocalRing.residue B)) := by
    have h1 := conj_mapEquiv_mem_rationalHomSet φ W hβ₀
    have h2 := WeierstrassCurve.comp_mem_rationalHomSet (IsLocalRing.ResidueField B)
      (E'.map (IsLocalRing.residue B)) (W.map φ.toRingHom) (W.map φ.toRingHom)
      (vcAddEquiv_symm_mem_rationalHomSet hv') h1
    have h3 := WeierstrassCurve.comp_mem_rationalHomSet (IsLocalRing.ResidueField B)
      (E'.map (IsLocalRing.residue B)) (W.map φ.toRingHom) (E'.map (IsLocalRing.residue B))
      h2 (vcAddEquiv_mem_rationalHomSet hv')
    exact h3
  have hβtchar : βt.comp βt + (m : ℤ) • AddMonoidHom.id _ = s • βt := conj_charPoly Tr hchar

  obtain ⟨φ', hφ'ker, hφ'⟩ :=
    (E'.map B.subtype).exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
      n hmΩ Q' hQ'
  haveI hVell : ((E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
      (E'.map B.subtype) n Q' hQ')⟩
  obtain ⟨hφ'rat, hφ'fac⟩ :=
    (E'.map B.subtype).veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
      n Q' hQ' φ' hφ'ker hφ'
  let eγ : ((E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Point ≃+
      (E'.map B.subtype).toAffine.Point := vcAddEquiv hγ
  have heγrat := vcAddEquiv_mem_rationalHomSet hγ
  have heγsymmrat := vcAddEquiv_symm_mem_rationalHomSet hγ
  let β' : (E'.map B.subtype).toAffine.Point →+ (E'.map B.subtype).toAffine.Point :=
    (eγ : _ →+ _).comp φ'
  have hβ'apply : ∀ P, β' P = eγ (φ' P) := fun P => rfl
  have hβ'rat : β' ∈ rationalHomSet Ω (E'.map B.subtype) (E'.map B.subtype) :=
    WeierstrassCurve.comp_mem_rationalHomSet Ω (E'.map B.subtype) _ (E'.map B.subtype) hφ'rat heγrat

  have hmid : ((m : ℤ) • AddMonoidHom.id (E'.map B.subtype).toAffine.Point) ∈
      rationalHomSet Ω (E'.map B.subtype) (E'.map B.subtype) := zsmul_id_mem_rationalHomSet _ (m : ℤ)
  have hmQ' : ((m : ℤ) • AddMonoidHom.id (E'.map B.subtype).toAffine.Point) Q' = 0 := by
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
    rw [natCast_zsmul, hmn, ← hQ', addOrderOf_nsmul_eq_zero]
  obtain ⟨ψ', hψ'rat, hψ'fac⟩ := hφ'fac (E'.map B.subtype) _ hmid hmQ'
  let ψ : ((E'.map B.subtype).veluQuotient ((E'.map B.subtype).oddOrderSummingSet Q' n)).toAffine.Point →+
      (E'.map B.subtype).toAffine.Point := ψ'
  have hψφ : ∀ P, ψ (φ' P) = (m : ℤ) • P := fun P => by
    have := DFunLike.congr_fun hψ'fac P
    first | simpa using this.symm | exact this.symm | (simp only [AddMonoidHom.comp_apply] at this; exact this.symm)
  have hφ'ne : φ' ≠ 0 := by
    intro h0
    obtain ⟨P, hP⟩ := exists_zsmul_ne_zero (E'.map B.subtype) hm0
    have hPker : P ∈ φ'.ker := by rw [h0]; exact AddMonoidHom.mem_ker.mpr rfl
    rw [hφ'ker] at hPker
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hPker
    apply hP
    rw [smul_comm, natCast_zsmul, hmn, ← hQ', addOrderOf_nsmul_eq_zero, zsmul_zero]
  have hφ'surj : Function.Surjective φ' :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet Ω hφ'rat hφ'ne
  have hφψ : ∀ X, φ' (ψ X) = (m : ℤ) • X := fun X => by
    obtain ⟨P, rfl⟩ := hφ'surj X
    rw [hψφ, map_zsmul]
  let βd : (E'.map B.subtype).toAffine.Point →+ (E'.map B.subtype).toAffine.Point :=
    ψ.comp (eγ.symm : _ →+ _)
  have hβdrat : βd ∈ rationalHomSet Ω (E'.map B.subtype) (E'.map B.subtype) :=
    WeierstrassCurve.comp_mem_rationalHomSet Ω (E'.map B.subtype) _ (E'.map B.subtype) heγsymmrat hψ'rat
  have hβ'βd : ∀ X, β' (βd X) = (m : ℤ) • X := fun X => by
    change eγ (φ' (ψ (eγ.symm X))) = _
    rw [hφψ, map_zsmul, AddEquiv.apply_symm_apply]
  have hβdβ' : ∀ P, βd (β' P) = (m : ℤ) • P := fun P => by
    change ψ (eγ.symm (eγ (φ' P))) = _
    rw [AddEquiv.symm_apply_apply, hψφ]

  obtain ⟨ν', hνrat, hνred, -⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom E' E' hΔ' hΔ' hβ'rat
  obtain ⟨νd', hνdrat, hνdred, -⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom E' E' hΔ' hΔ' hβdrat
  let ν : (E'.map (IsLocalRing.residue B)).toAffine.Point →+ (E'.map (IsLocalRing.residue B)).toAffine.Point := ν'
  let νd : (E'.map (IsLocalRing.residue B)).toAffine.Point →+ (E'.map (IsLocalRing.residue B)).toAffine.Point := νd'
  have hνapply : ∀ P, ν (WeierstrassCurve.reduceHom hΔ' P) = WeierstrassCurve.reduceHom hΔ' (β' P) :=
    fun P => (DFunLike.congr_fun hνred P).symm
  have hνdapply : ∀ P, νd (WeierstrassCurve.reduceHom hΔ' P) = WeierstrassCurve.reduceHom hΔ' (βd P) :=
    fun P => (DFunLike.congr_fun hνdred P).symm

  have hredsurj : Function.Surjective (WeierstrassCurve.reduceHom hΔ') :=
    WeierstrassCurve.reduceHom_surjective_of_henselianLocalRing hΔ'
  have hννd : ν.comp νd = (m : ℤ) • AddMonoidHom.id _ := by
    ext X
    obtain ⟨P, rfl⟩ := hredsurj X
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hνdapply, hνapply, hβ'βd, map_zsmul]
    rfl
  have hνdν : νd.comp ν = (m : ℤ) • AddMonoidHom.id _ := by
    ext X
    obtain ⟨P, rfl⟩ := hredsurj X
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hνapply, hνdapply, hβdβ', map_zsmul]
    rfl

  have hTrQ₀ : Tr Q₀ = WeierstrassCurve.reduceHom hΔ' Q' := by
    change e₁ (mapEquiv φ W Q₀) = _
    rw [DeuringTransport.mapEquiv_apply, hQ'red]
    exact (Affine.Point.equivOfVariableChangeEq hv').apply_symm_apply _
  have hmemTr : ∀ P : W.toAffine.Point, Tr P ∈ AddSubgroup.zmultiples (Tr Q₀) ↔
      P ∈ AddSubgroup.zmultiples Q₀ := by
    intro P
    constructor
    · intro h
      obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp h
      rw [← map_zsmul] at hj
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨j, Tr.injective hj⟩
    · intro h
      obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp h
      rw [map_zsmul]
      exact AddSubgroup.zsmul_mem_zmultiples _ j
  have hkerβt : βt.ker = AddSubgroup.zmultiples (WeierstrassCurve.reduceHom hΔ' Q') := by
    ext X
    obtain ⟨P, rfl⟩ := Tr.surjective X
    rw [mem_ker_conj_iff, AddEquiv.symm_apply_apply, hkerβ, ← hTrQ₀, hmemTr]
  have hνQ' : ν (WeierstrassCurve.reduceHom hΔ' Q') = 0 := by
    rw [hνapply, hβ'apply]
    have : φ' Q' = 0 := by
      rw [← AddMonoidHom.mem_ker, hφ'ker]; exact AddSubgroup.mem_zmultiples Q'
    rw [this, map_zero, map_zero]
  have hker : βt.ker ≤ ν.ker := by
    rw [hkerβt, AddSubgroup.zmultiples_le]
    exact hνQ'

  have hker' : m ≤ Nat.card νd.ker := by

    have hcardT : Nat.card (Submodule.torsionBy ℤ (E'.map B.subtype).toAffine.Point (m : ℤ)) = m ^ 2 :=
      WeierstrassCurve.card_torsion_of_isAlgClosed (K := Ω) (E'.map B.subtype) hmΩ'
    have hkerβ' : β'.ker = AddSubgroup.zmultiples Q' := by
      rw [← hφ'ker]
      ext P
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hβ'apply, map_eq_zero_iff _ eγ.injective]
    have hQ'm : addOrderOf Q' = m := hQ'.trans hmn.symm
    have hX : Nat.card (β'.comp (Submodule.torsionBy ℤ (E'.map B.subtype).toAffine.Point
        (m : ℤ)).toAddSubgroup.subtype).range = m :=
      card_range_torsion β' hn0 Q' hQ'm hkerβ' hcardT
    set X := (β'.comp (Submodule.torsionBy ℤ (E'.map B.subtype).toAffine.Point
        (m : ℤ)).toAddSubgroup.subtype).range with hXdef

    have hcardTt : Nat.card (Submodule.torsionBy ℤ (E'.map (IsLocalRing.residue B)).toAffine.Point (m : ℤ))
        = m ^ 2 :=
      WeierstrassCurve.card_torsion_of_isAlgClosed (K := IsLocalRing.ResidueField B)
        (E'.map (IsLocalRing.residue B)) hmκ
    haveI : Finite (Submodule.torsionBy ℤ (E'.map (IsLocalRing.residue B)).toAffine.Point (m : ℤ)) :=
      Nat.finite_of_card_ne_zero (by rw [hcardTt]; exact pow_ne_zero 2 hn0)
    have hkerle : νd.ker ≤ (Submodule.torsionBy ℤ (E'.map (IsLocalRing.residue B)).toAffine.Point
        (m : ℤ)).toAddSubgroup := by
      intro X hX
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
      have := DFunLike.congr_fun hννd X
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, (AddMonoidHom.mem_ker).mp hX, map_zero] at this
      exact this.symm
    haveI : Finite νd.ker := Finite.of_injective _ (AddSubgroup.inclusion_injective hkerle)

    have hXtors : ∀ x : X, m • (x : (E'.map B.subtype).toAffine.Point) = 0 := by
      rintro ⟨x, hx⟩
      obtain ⟨⟨t, ht⟩, rfl⟩ := AddMonoidHom.mem_range.mp hx
      simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply]
      rw [← natCast_zsmul, ← map_zsmul]
      have ht' : (m : ℤ) • t = 0 := ht
      rw [ht', map_zero]
    have hXker : ∀ x : X, WeierstrassCurve.reduceHom hΔ' (x : (E'.map B.subtype).toAffine.Point) ∈ νd.ker := by
      rintro ⟨x, hx⟩
      obtain ⟨⟨t, ht⟩, rfl⟩ := AddMonoidHom.mem_range.mp hx
      rw [AddMonoidHom.mem_ker]
      simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply]
      rw [hνdapply, hβdβ']
      have ht' : (m : ℤ) • t = 0 := ht
      rw [ht', map_zero]
    let f : X → νd.ker := fun x => ⟨WeierstrassCurve.reduceHom hΔ' (x : (E'.map B.subtype).toAffine.Point), hXker x⟩
    have hf : Function.Injective f := by
      intro x₁ x₂ h12
      have h := congrArg Subtype.val h12
      exact Subtype.ext (WeierstrassCurve.eq_of_reduceHom_eq_of_nsmul_eq_zero hΔ' hmκ (hXtors x₁) (hXtors x₂) h)
    calc m = Nat.card X := hX.symm
      _ ≤ Nat.card νd.ker := Nat.card_le_card_of_injective f hf

  obtain ⟨ε, hε, ε', hε', hε'ε, hεε', hνfac⟩ :=
    (E'.map (IsLocalRing.residue B)).exists_unit_rationalHomSet_comp_eq_of_ker_le_of_comp_eq_smul_id
      hβtrat s m hβtchar hirr hprim hmκ ⟨n, hn⟩ hνrat hνdrat hννd hνdν hker hker'
  let ε₀ : (E'.map (IsLocalRing.residue B)).toAffine.Point →+ (E'.map (IsLocalRing.residue B)).toAffine.Point := ε
  have hνε : ∀ X, ν X = ε₀ (βt X) := fun X => by
    have := DFunLike.congr_fun hνfac X
    exact this

  have hβ₀ne : β₀ ≠ 0 := by
    intro h0
    obtain ⟨P, hP⟩ := exists_zsmul_ne_zero W hm0
    have := DFunLike.congr_fun hchar P
    simp only [h0, AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.zero_apply, zero_add, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, smul_zero] at this
    exact hP this
  have hβtne : βt ≠ 0 := by
    intro h0
    apply hβ₀ne
    ext P
    have := hβt_apply P
    rw [h0, AddMonoidHom.zero_apply] at this
    have h' : β₀ P = 0 := Tr.injective (by rw [← this, map_zero])
    rw [h', AddMonoidHom.zero_apply]
  have hβtsurj : Function.Surjective βt :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet (IsLocalRing.ResidueField B) hβtrat hβtne
  have hmredQ' : (m : ℤ) • WeierstrassCurve.reduceHom hΔ' Q' = 0 := by
    rw [← map_zsmul, natCast_zsmul, hmn, ← hQ', addOrderOf_nsmul_eq_zero, map_zero]
  have hεfix : ∀ T : (E'.map (IsLocalRing.residue B)).toAffine.Point, (ℓ : ℤ) • T = 0 → ε₀ T = T := by
    intro T hT
    by_cases hT0 : T = 0
    · rw [hT0, map_zero]
    obtain ⟨Pt, hPt⟩ := hβtsurj T

    have hPtnot : Pt ∉ AddSubgroup.zmultiples (WeierstrassCurve.reduceHom hΔ' Q') := by
      intro hmem
      rw [← hkerβt] at hmem
      exact hT0 (hPt ▸ ((AddMonoidHom.mem_ker).mp hmem))
    have hℓPt : (ℓ : ℤ) • Pt ∈ AddSubgroup.zmultiples (WeierstrassCurve.reduceHom hΔ' Q') := by
      rw [← hkerβt, AddMonoidHom.mem_ker, map_zsmul, hPt, hT]
    obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hℓPt

    have hℓmκ : ((ℓ * m : ℕ) : IsLocalRing.ResidueField B) ≠ 0 := by
      rw [Nat.cast_mul]; exact mul_ne_zero hℓκ hmκ
    have hPttors : (ℓ * m) • Pt = 0 := by
      have e : (ℓ * m) • Pt = (m : ℤ) • ((ℓ : ℤ) • Pt) := by
        rw [← natCast_zsmul, Nat.cast_mul, mul_comm, mul_zsmul]
      rw [e]
      change (m : ℤ) • ((ℓ : ℤ) • Pt) = 0
      rw [← hj, smul_comm, hmredQ', zsmul_zero]
    obtain ⟨P', hP'tors, hP'red⟩ := exists_torsion_lift hΔ' hℓmκ Pt hPttors

    have hℓP' : (ℓ : ℤ) • P' ∈ AddSubgroup.zmultiples Q' := by
      refine AddSubgroup.mem_zmultiples_iff.mpr ⟨j, ?_⟩
      refine WeierstrassCurve.eq_of_reduceHom_eq_of_nsmul_eq_zero hΔ' hmκ (N := m) ?_ ?_ ?_
      · rw [smul_comm, hmn, ← hQ', addOrderOf_nsmul_eq_zero, zsmul_zero]
      · have e : (ℓ : ℤ) • (m • P') = (ℓ * m) • P' := by
          rw [← natCast_zsmul P' m, smul_smul, ← Nat.cast_mul, natCast_zsmul]
        rw [smul_comm, e, hP'tors]
      · rw [map_zsmul, map_zsmul, hP'red, hj]

    set Pb := Tr.symm Pt with hPbdef
    have hTrPb : Tr Pb = Pt := Tr.apply_symm_apply Pt
    have hPbnot : Pb ∉ AddSubgroup.zmultiples Q₀ := by
      rw [← hmemTr, hTrPb, hTrQ₀]; exact hPtnot
    have hℓPb : (ℓ : ℤ) • Pb ∈ AddSubgroup.zmultiples Q₀ := by
      rw [← hmemTr, map_zsmul, hTrPb, hTrQ₀]; exact hℓPt
    have hP'ne : P' ≠ 0 := by
      intro h0; apply hT0
      rw [← hPt, ← hP'red, h0, map_zero, map_zero]
    have hPbne : Pb ≠ 0 := by
      intro h0; apply hT0
      rw [← hPt, ← hTrPb, h0, map_zero, map_zero]
    have hP'not : P' ∉ AddSubgroup.zmultiples Q' := by
      intro hmem
      obtain ⟨i, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
      apply hPtnot
      rw [← hP'red, map_zsmul]
      exact AddSubgroup.zsmul_mem_zmultiples _ i
    rcases hPb : Pb with _ | ⟨x, y, hxy⟩
    · exact absurd hPb hPbne
    rcases hP'c : P' with _ | ⟨x', y', hxy'⟩
    · exact absurd hP'c hP'ne
    rw [hPb] at hPbnot hℓPb hTrPb
    rw [hP'c] at hP'not hP'red hℓP'

    have hrel : WeierstrassCurve.ratPointHom φ.toRingHom (.some x y hxy) =
        (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm
          (WeierstrassCurve.reduceHom hΔ' (.some x' y' hxy')) := by
      rw [hP'red, ← hTrPb]
      change _ = e₁.symm (e₁ (mapEquiv φ W _))
      rw [AddEquiv.symm_apply_apply]
      rfl
    obtain ⟨h'', h₀'', HEQ⟩ := HMS x' y' hxy' x y hxy hℓPb hPbnot hℓP' hrel

    obtain ⟨h₁, e₁'⟩ := hφb x y hxy hPbnot
    have hL : WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ₀
        (.some _ _ h₀'') = β₀ (.some x y hxy) := by
      rw [hβ₀fac, e₁']
    obtain ⟨h₂, e₂'⟩ := hφ' x' y' hxy' hP'not
    have hR : WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ (.some _ _ h'') =
        β' (.some x' y' hxy') := by
      rw [hβ'apply, e₂']
      rfl
    rw [hL, hR] at HEQ

    have HEQ' : Tr (β₀ (.some x y hxy)) = WeierstrassCurve.reduceHom hΔ' (β' (.some x' y' hxy')) := by
      change e₁ (mapEquiv φ W (β₀ _)) = _
      rw [DeuringTransport.mapEquiv_apply, HEQ]
      exact (Affine.Point.equivOfVariableChangeEq hv').apply_symm_apply _
    rw [← hβt_apply, hTrPb, hPt, ← hνapply, hP'red, hνε, hPt] at HEQ'
    exact HEQ'.symm

  have hsign : ∃ σ : ℤ, σ * σ = 1 ∧ ∀ X, ν X = σ • βt X := by
    rcases hℓ23 with rfl | rfl
    · have h2κ : (2 : IsLocalRing.ResidueField B) ≠ 0 := by exact_mod_cast hℓκ
      rcases (E'.map (IsLocalRing.residue B)).eq_id_or_eq_neg_id_of_comp_eq_id_of_forall_two_torsion_apply_eq_self
          (IsLocalRing.ResidueField B) h2κ hε hε' hε'ε hεε' (fun P hP => hεfix P (by exact_mod_cast hP))
        with h1 | h1
      · refine ⟨1, by norm_num, fun X => ?_⟩
        rw [hνε, one_zsmul]
        exact DFunLike.congr_fun h1 (βt X)
      · refine ⟨-1, by norm_num, fun X => ?_⟩
        rw [hνε, neg_one_zsmul]
        exact DFunLike.congr_fun h1 (βt X)
    · have h3κ : ((3 : ℕ) : IsLocalRing.ResidueField B) ≠ 0 := hℓκ
      have h1 := (E'.map (IsLocalRing.residue B)).eq_id_of_comp_eq_id_of_forall_torsion_apply_eq_self
          (IsLocalRing.ResidueField B) (N := 3) le_rfl h3κ hε hε' hε'ε hεε' (fun P hP => hεfix P hP)
      refine ⟨1, by norm_num, fun X => ?_⟩
      rw [hνε, one_zsmul]
      exact DFunLike.congr_fun h1 (βt X)
  obtain ⟨σ, hσσ, hνσ⟩ := hsign

  have halg : IsAlgebraic ℚ (E'.map B.subtype).j :=
    isAlgebraic_j_of_smul_eq_veluQuotient (E'.map B.subtype) n hsq' Q' hQ' γ hγ

  refine ⟨B, φ, E', hE', hΔ', halg, v', hv', σ • β', zsmul_mem_rationalHomSet hβ'rat σ, ?_⟩
  intro Q P₀ hQP
  have hTrP₀ : Tr P₀ = WeierstrassCurve.reduceHom hΔ' Q := by
    change e₁ (mapEquiv φ W P₀) = _
    rw [DeuringTransport.mapEquiv_apply, hQP]
    exact (Affine.Point.equivOfVariableChangeEq hv').apply_symm_apply _
  have key : Tr (β₀ P₀) = WeierstrassCurve.reduceHom hΔ' ((σ • β') Q) := by
    rw [AddMonoidHom.smul_apply, map_zsmul, ← hνapply, ← hTrP₀, hνσ, smul_smul, hσσ, one_zsmul,
      hβt_apply]
  have key' : mapEquiv φ W (β₀ P₀) = e₁.symm (WeierstrassCurve.reduceHom hΔ' ((σ • β') Q)) := by
    rw [← key]
    change _ = e₁.symm (e₁ _)
    rw [AddEquiv.symm_apply_apply]
    rfl
  exact key'

end WeierstrassCurve.DeuringLocal

open scoped Classical in
theorem solution (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic] {β₀ : W.toAffine.Point →+ W.toAffine.Point} (hβ₀ : β₀ ∈ WeierstrassCurve.rationalHomSet k W W) (s : ℤ) (m : ℕ) (hchar : β₀.comp β₀ + (m : ℤ) • AddMonoidHom.id _ = s • β₀) (hirr : ∀ x : ℤ, x ^ 2 - s * x + m ≠ 0) (hprim : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ s → ¬ (ℓ : ℤ) ^ 2 ∣ (m : ℤ)) (hm : (m : k) ≠ 0) (hodd : Odd m) (hsq : ¬ IsSquare m) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra (FractionRing (WittVector p k)) Ω] [Algebra.IsAlgebraic (FractionRing (WittVector p k)) Ω] : ∃ (B : ValuationSubring Ω) (φ : k ≃+* IsLocalRing.ResidueField B) (E' : WeierstrassCurve B) (_ : E'.IsElliptic) (hΔ' : (E'.map (IsLocalRing.residue B)).Δ ≠ 0) (_ : IsAlgebraic ℚ (E'.map B.subtype).j) (v' : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField B)) (hv' : v' • E'.map (IsLocalRing.residue B) = W.map φ.toRingHom), ∃ β' ∈ WeierstrassCurve.rationalHomSet Ω (E'.map B.subtype) (E'.map B.subtype), ∀ (Q : (E'.map B.subtype).toAffine.Point) (P₀ : W.toAffine.Point), WeierstrassCurve.ratPointHom φ.toRingHom P₀ = (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm (WeierstrassCurve.reduceHom hΔ' Q) → WeierstrassCurve.ratPointHom φ.toRingHom (β₀ P₀) = (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv').symm (WeierstrassCurve.reduceHom hΔ' (β' Q)) :=
  WeierstrassCurve.DeuringLocal.main p W hβ₀ s m hchar hirr hprim hm hodd hsq Ω

end S_WeierstrassCurve_exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_valuationSubring_residueField_equiv_and_reduceHom_comp_eq_of_isAlgClosed_of_comp_self_add_smul_eq_smul (solution)
