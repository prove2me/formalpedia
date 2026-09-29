-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a298745d-47ad-5dc8-b936-08185eeba59c

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.kohelW_one Polynomial.rootESymm_zero_right WeierstrassCurve.kohelQuotient_a₂ WeierstrassCurve.kohelQuotient_a₃ WeierstrassCurve.kohelT_one WeierstrassCurve.kohelQuotient_one WeierstrassCurve.kohelQuotient_a₁ Polynomial.rootESymm_one"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.legendreVariableChange_s WeierstrassCurve.legendreVariableChange_t WeierstrassCurve.legendreVariableChange_r WeierstrassCurve.legendreVariableChange_u ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.deuringVariableChange_s WeierstrassCurve.deuringVariableChange_t WeierstrassCurve.deuringCurve_a₄ WeierstrassCurve.deuringCurve_a₂ WeierstrassCurve.deuringCurve_a₆ WeierstrassCurve.deuringCurve_a₁ WeierstrassCurve.deuringVariableChange_u WeierstrassCurve.deuringCurve_a₃ WeierstrassCurve.deuringVariableChange_r WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"

set_option autoImplicit false

p2m_open "IsLocalRing WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ a₁ map b₂ isElliptic_iff a₄ a₂ a₆ isIntegral_iff reduction IsIntegral toAffine Affine.Point map_Δ b₆ Δ VariableChange Affine.Point.neg_some baseChange b₄ evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet reduceHom map_residue_Δ_ne_zero_iff Affine.Point.variableChangeEquiv Affine.Point.equivOfVariableChangeEq comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed Affine.Point.vcInvFun_add exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul"
namespace DeuringLiftGeneral
p2m_open "WeierstrassCurve"

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
    (hα : α ∈ rationalHomSet k W W) (M N : ℤ) :
    M • α + N • AddMonoidHom.id _ ∈ rationalHomSet k W W :=
  WeierstrassCurve.add_mem_rationalHomSet k W W (zsmul_mem_rationalHomSet hα M)
    (zsmul_id_mem_rationalHomSet W N)

theorem quadratic_mem_rationalHomSet {W : WeierstrassCurve F} [W.IsElliptic]
    {α : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W W) (t q : ℤ) :
    α.comp α + q • AddMonoidHom.id _ - t • α ∈ rationalHomSet k W W :=
  sub_mem_rationalHomSet
    (WeierstrassCurve.add_mem_rationalHomSet k W W
      (WeierstrassCurve.comp_mem_rationalHomSet k W W W hα hα)
      (zsmul_id_mem_rationalHomSet W q))
    (zsmul_mem_rationalHomSet hα t)

end HomSet

section NonTorsion

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

theorem exists_zsmul_ne_zero (p : ℕ) [Fact p.Prime] [CharP k p] {M : ℤ} (hM : M ≠ 0) :
    ∃ P : W.toAffine.Point, M • P ≠ 0 := by

  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (M.natAbs + p + 1)
  have hℓM : ¬ (ℓ : ℤ) ∣ M := by
    intro h
    have h1 : ℓ ≤ M.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hM) (Int.natCast_dvd.mp h)
    omega
  have hℓp : ℓ ≠ p := by
    intro h; subst h; omega
  have hℓk : (ℓ : k) ≠ 0 := by
    intro h
    have hdvd : p ∣ ℓ := (CharP.cast_eq_zero_iff k p ℓ).mp h
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).mp hdvd
    exact hℓp this.symm

  have hcard : Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed W hℓk
  have hgt : 1 < Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) := by
    rw [hcard]
    have := hℓ.one_lt
    nlinarith
  haveI : Finite (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) :=
    Nat.finite_of_card_ne_zero (by omega)
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

theorem eq_zero_of_zsmul_apply_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p]
    {ε : W.toAffine.Point →+ W.toAffine.Point}
    (hε : ε ∈ rationalHomSet k W W) {M : ℤ} (hM : M ≠ 0) (h : ∀ P, M • ε P = 0) : ε = 0 := by
  by_contra hne
  have hsurj : Function.Surjective ε := WeierstrassCurve.surjective_of_mem_rationalHomSet k hε hne
  obtain ⟨P, hP⟩ := exists_zsmul_ne_zero W p hM
  obtain ⟨Q, rfl⟩ := hsurj P
  exact hP (h Q)

end NonTorsion

section CharPoly

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

theorem charPoly_apply {G : Type*} [AddCommGroup G] {β : G →+ G} {t q : ℤ}
    (h : β.comp β + q • AddMonoidHom.id _ = t • β) (P : G) : β (β P) + q • P = t • β P := by
  have := DFunLike.congr_fun h P
  simpa using this

theorem forall_ne_zero_of_not_scalar {β : W.toAffine.Point →+ W.toAffine.Point}
    (hβ : β ∈ rationalHomSet k W W) {t q : ℤ} (hchar : β.comp β + q • AddMonoidHom.id _ = t • β)
    (hns : ¬ ∃ N : ℤ, β = N • AddMonoidHom.id _) (m : ℤ) : m ^ 2 - t * m + q ≠ 0 := by
  intro hm
  set δ : W.toAffine.Point →+ W.toAffine.Point := β - m • AddMonoidHom.id _ with hδ
  have hδmem : δ ∈ rationalHomSet k W W :=
    sub_mem_rationalHomSet (k := k) hβ (zsmul_id_mem_rationalHomSet W m)

  have hkill : ∀ P, β (δ P) - (t - m) • δ P = 0 := by
    intro P
    have e1 := charPoly_apply hchar P
    have e2 : δ P = β P - m • P := by simp [hδ]
    have hq : q = t * m - m ^ 2 := by linarith
    rw [e2, map_sub, map_zsmul]
    have e3 : β (β P) = t • β P - q • P := eq_sub_of_add_eq e1
    rw [e3, hq]
    module
  by_cases hδ0 : δ = 0
  · exact hns ⟨m, sub_eq_zero.mp hδ0⟩
  · have hsurj : Function.Surjective δ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hδmem hδ0
    apply hns
    refine ⟨t - m, ?_⟩
    ext P
    obtain ⟨Q, rfl⟩ := hsurj P
    have := hkill Q
    rw [sub_eq_zero] at this
    simpa using this

theorem disc_ne_zero {t q : ℤ} (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) : t ^ 2 - 4 * q ≠ 0 := by
  intro h

  have ht : 2 ∣ t := by
    have h2 : (2 : ℤ) ∣ t ^ 2 := ⟨2 * q, by linarith⟩
    exact Int.Prime.dvd_pow' (by norm_num) h2
  obtain ⟨m, rfl⟩ := ht
  exact hirr m (by nlinarith)

theorem charPoly_recentre (p : ℕ) [Fact p.Prime] [CharP k p] {β γ : W.toAffine.Point →+ W.toAffine.Point}
    (hγ : γ ∈ rationalHomSet k W W) {t q : ℤ} (hchar : β.comp β + q • AddMonoidHom.id _ = t • β)
    {k₀ t' q' : ℤ} (ht : t - 2 * k₀ = p * t') (hq : k₀ ^ 2 - t * k₀ + q = p ^ 2 * q')
    (hβγ : β - k₀ • AddMonoidHom.id _ = (p : ℤ) • γ) :
    γ.comp γ + q' • AddMonoidHom.id _ = t' • γ := by
  set ε : W.toAffine.Point →+ W.toAffine.Point := γ.comp γ + q' • AddMonoidHom.id _ - t' • γ
    with hεdef
  have hε : ε ∈ rationalHomSet k W W := quadratic_mem_rationalHomSet (k := k) hγ t' q'
  have hp0 : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have key : ∀ P, ((p : ℤ) ^ 2) • ε P = 0 := by
    intro P
    have eδ : ∀ Q, β Q - k₀ • Q = (p : ℤ) • γ Q := fun Q => by
      have := DFunLike.congr_fun hβγ Q
      simpa using this
    have e1 := charPoly_apply hchar P

    have e2 : ((p : ℤ) ^ 2) • γ (γ P) = β (β P) - k₀ • β P - k₀ • β P + (k₀ * k₀) • P := by
      have h1 : (p : ℤ) • γ ((p : ℤ) • γ P) = ((p : ℤ) ^ 2) • γ (γ P) := by
        rw [map_zsmul, smul_smul, sq]
      rw [← h1, ← eδ P, map_sub, map_zsmul, smul_sub, ← eδ (β P), smul_comm (p : ℤ) k₀ (γ P),
        ← eδ P]
      module
    have e3 : β (β P) = t • β P - q • P := eq_sub_of_add_eq e1
    have e4 : (p : ℤ) • γ P = β P - k₀ • P := (eδ P).symm
    simp only [hεdef, AddMonoidHom.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
      Function.comp_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply]
    have htt : t = 2 * k₀ + p * t' := by linarith
    have hqq : q = p ^ 2 * q' - k₀ ^ 2 + t * k₀ := by linarith
    calc ((p : ℤ) ^ 2) • (γ (γ P) + q' • P - t' • γ P)
        = ((p : ℤ) ^ 2) • γ (γ P) + ((p : ℤ) ^ 2 * q') • P - ((p : ℤ) * t') • ((p : ℤ) • γ P) := by
          module
      _ = (β (β P) - k₀ • β P - k₀ • β P + (k₀ * k₀) • P) + ((p : ℤ) ^ 2 * q') • P
            - ((p : ℤ) * t') • (β P - k₀ • P) := by rw [e2, e4]
      _ = 0 := by
          rw [e3, hqq, htt]
          module
  exact sub_eq_zero.mp (eq_zero_of_zsmul_apply_eq_zero W p hε hp0 key)

end CharPoly

section Place

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_coe_eq_of_monic_aeval_eq_zero {P : A[X]} (hP : P.Monic) {z : L}
    (hz : aeval z P = 0) : ∃ a : A, (a : L) = z := by
  have hint : _root_.IsIntegral A z := ⟨P, hP, by rwa [aeval_def] at hz⟩
  exact (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp hint

theorem isAlgClosed_residueField [IsAlgClosed L] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hlift : p ∈ Polynomial.lifts (residue A) :=
    (Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ residue_surjective p)
  obtain ⟨P, hPp, hdeg, hPmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  have hdeg' : (P.map (algebraMap A L)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective Subtype.val_injective]
    intro h0
    have h1 := hirr.natDegree_pos
    rw [← hdeg, Polynomial.natDegree_eq_of_degree_eq_some
      (show P.degree = ((0 : ℕ) : WithBot ℕ) from h0)] at h1
    exact lt_irrefl _ h1
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (P.map (algebraMap A L)) hdeg'
  have hz' : aeval z P = 0 := by rwa [Polynomial.IsRoot, Polynomial.eval_map, ← aeval_def] at hz
  obtain ⟨a, rfl⟩ := exists_coe_eq_of_monic_aeval_eq_zero A hPmon hz'
  refine ⟨residue A a, ?_⟩
  have hPa : P.eval a = 0 := by
    have h1 : algebraMap A L (aeval a P) = 0 := by
      rw [← Polynomial.aeval_algebraMap_apply]; exact hz'
    rw [map_eq_zero_iff _ Subtype.val_injective, Polynomial.coe_aeval_eq_eval] at h1
    exact h1
  rw [← hPp, Polynomial.eval_map, Polynomial.eval₂_hom, hPa, _root_.map_zero]

end Place

section Model

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem isElliptic_map_subtype (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) :
    (E.map A.subtype).IsElliptic := by
  have hu : IsUnit E.Δ := (map_residue_Δ_ne_zero_iff E).mp hΔ
  rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
  exact hu.map A.subtype

theorem exists_map_residue_eq (V : WeierstrassCurve (ResidueField A)) :
    ∃ E : WeierstrassCurve A, E.map (residue A) = V := by
  obtain ⟨b₁, h₁⟩ := residue_surjective (R := A) V.a₁
  obtain ⟨b₂, h₂⟩ := residue_surjective (R := A) V.a₂
  obtain ⟨b₃, h₃⟩ := residue_surjective (R := A) V.a₃
  obtain ⟨b₄, h₄⟩ := residue_surjective (R := A) V.a₄
  obtain ⟨b₆, h₆⟩ := residue_surjective (R := A) V.a₆
  refine ⟨⟨b₁, b₂, b₃, b₄, b₆⟩, ?_⟩
  obtain ⟨a₁, a₂, a₃, a₄, a₆⟩ := V
  simp only [WeierstrassCurve.map] at *
  rw [h₁, h₂, h₃, h₄, h₆]

variable {K : Type*} [Field K] [DecidableEq K]

theorem equivOfVariableChangeEq_rfl (C : VariableChange K) (X : WeierstrassCurve.Affine K) :
    Affine.Point.equivOfVariableChangeEq (rfl : C • X = C • X) = Affine.Point.variableChangeEquiv C X :=
  rfl

theorem equivOfVariableChangeEq_symm_add (C : VariableChange K) (X : WeierstrassCurve.Affine K)
    {V : WeierstrassCurve.Affine K} (h : C • X = V) (P Q : X.Point) :
    (Affine.Point.equivOfVariableChangeEq h).symm (P + Q) =
      (Affine.Point.equivOfVariableChangeEq h).symm P + (Affine.Point.equivOfVariableChangeEq h).symm Q := by
  subst h
  exact WeierstrassCurve.Affine.Point.vcInvFun_add C X P Q

noncomputable def vStar (C : VariableChange K) (X : WeierstrassCurve.Affine K)
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

local notation "κ" => ResidueField A
local notation "ℚbar" => AlgebraicClosure ℚ

def Liftable (W : WeierstrassCurve κ) (α₀ : W.toAffine.Point →+ W.toAffine.Point) : Prop :=
  ∃ (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) (v : VariableChange κ)
    (hv : v • E.map (residue A) = W),
    ∃ α ∈ rationalHomSet ℚbar (E.map A.subtype) (E.map A.subtype),
      ∀ P : (E.map A.subtype).toAffine.Point,
        (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ (α P)) =
          α₀ ((Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ P))

variable {A}

theorem Liftable.affine {W : WeierstrassCurve κ} {β₀ : W.toAffine.Point →+ W.toAffine.Point}
    (h : Liftable A W β₀) (M N : ℤ) : Liftable A W (M • β₀ + N • AddMonoidHom.id _) := by
  obtain ⟨E, hΔ, v, hv, β, hβ, hcomm⟩ := h
  haveI := isElliptic_map_subtype E hΔ
  refine ⟨E, hΔ, v, hv, M • β + N • AddMonoidHom.id _, ?_, fun P => ?_⟩
  · exact affine_mem_rationalHomSet (k := ℚbar) (W := E.map A.subtype) hβ M N
  ·

    set T : ((E.map A.subtype).baseChange ℚbar).toAffine.Point →+ W.toAffine.Point :=
      (vStar v (E.map (residue A)) hv).comp (reduceHom hΔ) with hT
    have hT' : ∀ Q, (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ Q) = T Q :=
      fun Q => rfl
    have hcomm' : ∀ Q, T (β Q) = β₀ (T Q) := fun Q => by rw [← hT', ← hT']; exact hcomm Q
    rw [hT', hT']
    simp only [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, map_add,
      map_zsmul, hcomm']

theorem liftable_zsmul_id (W : WeierstrassCurve κ) [W.IsElliptic] (N : ℤ) :
    Liftable A W (N • AddMonoidHom.id _) := by
  obtain ⟨E, hred⟩ := exists_map_residue_eq (A := A) W
  have hΔ : (E.map (residue A)).Δ ≠ 0 := by rw [hred]; exact W.isUnit_Δ.ne_zero
  haveI := isElliptic_map_subtype E hΔ
  have hv : (1 : VariableChange κ) • E.map (residue A) = W := by rw [one_smul]; exact hred
  refine ⟨E, hΔ, 1, hv, N • AddMonoidHom.id _, zsmul_id_mem_rationalHomSet (k := ℚbar) _ N,
    fun P => ?_⟩
  set T : ((E.map A.subtype).baseChange ℚbar).toAffine.Point →+ W.toAffine.Point :=
    (vStar 1 (E.map (residue A)) hv).comp (reduceHom hΔ) with hT
  have hT' : ∀ Q, (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ Q) = T Q :=
    fun Q => rfl
  rw [hT', hT']
  simp only [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, map_zsmul]

theorem Liftable.congr {W : WeierstrassCurve κ} {α α' : W.toAffine.Point →+ W.toAffine.Point}
    (h : Liftable A W α) (e : α = α') : Liftable A W α' := e ▸ h

theorem liftable_of_charPoly (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (W : WeierstrassCurve κ) [W.IsElliptic] (D : ℕ) :
    ∀ (β₀ : W.toAffine.Point →+ W.toAffine.Point), β₀ ∈ rationalHomSet κ W W →
      (¬ ∃ N : ℤ, β₀ = N • AddMonoidHom.id _) →
      ∀ t q : ℤ, β₀.comp β₀ + q • AddMonoidHom.id _ = t • β₀ → (t ^ 2 - 4 * q).natAbs = D →
        Liftable A W β₀ := by
  haveI : IsAlgClosed κ := isAlgClosed_residueField A
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro β₀ hβ₀ hns t q hchar hD
  have hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0 := forall_ne_zero_of_not_scalar W hβ₀ hchar hns
  by_cases hmax : ∀ k₀ : ℤ, (p : ℤ) ∣ t - 2 * k₀ → ¬ (p : ℤ) ^ 2 ∣ k₀ ^ 2 - t * k₀ + q
  ·
    exact WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_comp_self_add_smul_eq_smul
      p A W hβ₀ t q hchar hirr hmax
  ·
    push Not at hmax
    obtain ⟨k₀, h₁, h₂⟩ := hmax
    obtain ⟨γ₁, hγ₁, hγeq₁⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
        p W hβ₀ t q hchar k₀ h₁ h₂

    let γ : W.toAffine.Point →+ W.toAffine.Point := γ₁
    have hγ : γ ∈ rationalHomSet κ W W := hγ₁
    have hγeq : β₀ - k₀ • AddMonoidHom.id W.toAffine.Point = (p : ℤ) • γ := hγeq₁
    have hβeq : β₀ = (p : ℤ) • γ + k₀ • AddMonoidHom.id W.toAffine.Point := by
      ext P
      have e := DFunLike.congr_fun hγeq P
      simp only [AddMonoidHom.sub_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply] at e
      simp only [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply]
      rw [← e]
      abel
    obtain ⟨t', ht'⟩ := h₁
    obtain ⟨q', hq'⟩ := h₂

    have hγns : ¬ ∃ N : ℤ, γ = N • AddMonoidHom.id _ := by
      rintro ⟨N, hN⟩
      apply hns
      refine ⟨(p : ℤ) * N + k₀, ?_⟩
      ext P
      have e := DFunLike.congr_fun hβeq P
      rw [hN] at e
      simp only [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply] at e ⊢
      rw [e, ← mul_zsmul, ← add_zsmul]

    have hcharγ : γ.comp γ + q' • AddMonoidHom.id _ = t' • γ :=
      charPoly_recentre W p hγ hchar ht' hq' hγeq
    have hdisc : t ^ 2 - 4 * q = (p : ℤ) ^ 2 * (t' ^ 2 - 4 * q') := by
      have htt : t = 2 * k₀ + p * t' := by linarith
      have hqq : q = p ^ 2 * q' - k₀ ^ 2 + t * k₀ := by linarith
      rw [hqq, htt]; ring
    have hD' : (t' ^ 2 - 4 * q').natAbs < D := by
      have hne : t' ^ 2 - 4 * q' ≠ 0 := by
        intro h0
        exact disc_ne_zero hirr (by rw [hdisc, h0, mul_zero])
      rw [← hD, hdisc, Int.natAbs_mul, Int.natAbs_pow]
      have hp1 : 1 < (p : ℤ).natAbs ^ 2 := by
        rw [Int.natAbs_natCast]
        have := (Fact.out : p.Prime).one_lt
        nlinarith
      have hpos : 0 < (t' ^ 2 - 4 * q').natAbs := Int.natAbs_pos.mpr hne
      nlinarith
    have hliftγ : Liftable A W γ := ih _ hD' γ hγ hγns t' q' hcharγ rfl

    exact (hliftγ.affine (p : ℤ) k₀).congr hβeq.symm

theorem liftable (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p] (W : WeierstrassCurve κ) [W.IsElliptic]
    {α₀ : W.toAffine.Point →+ W.toAffine.Point} (hα₀ : α₀ ∈ rationalHomSet κ W W) :
    Liftable A W α₀ := by
  haveI : IsAlgClosed κ := isAlgClosed_residueField A
  by_cases hns : ∃ N : ℤ, α₀ = N • AddMonoidHom.id _
  · obtain ⟨N, rfl⟩ := hns
    exact liftable_zsmul_id W N
  ·
    have hα0 : α₀ ≠ 0 := by
      rintro rfl; exact hns ⟨0, by ext P; simp⟩
    obtain ⟨σ, -, t, n, -, hdual, htr⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_isDualPair_and_add_eq_smul_id κ W hα₀ hα0

    let σ' : W.toAffine.Point →+ W.toAffine.Point := σ
    have hchar : α₀.comp α₀ + n • AddMonoidHom.id _ = t • α₀ := by
      ext P

      have h2 : α₀ (α₀ P) + σ' (α₀ P) = t • α₀ P := DFunLike.congr_fun htr (α₀ P)
      have h3 : σ' (α₀ P) = n • P := hdual.comp_left P
      rw [h3] at h2
      simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply]
      exact h2
    exact liftable_of_charPoly p W _ α₀ hα₀ hns t n hchar rfl

end Lift

end WeierstrassCurve.DeuringLiftGeneral
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet.WeierstrassCurve.DeuringLiftGeneral"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet.WeierstrassCurve"

open WeierstrassCurve.DeuringLiftGeneral in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p] (W : WeierstrassCurve (IsLocalRing.ResidueField A)) [W.IsElliptic] {α₀ : W.toAffine.Point →+ W.toAffine.Point} (hα₀ : α₀ ∈ WeierstrassCurve.rationalHomSet (IsLocalRing.ResidueField A) W W) : ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv : v • E.map (IsLocalRing.residue A) = W), ∃ α ∈ WeierstrassCurve.rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype), ∀ P : (E.map A.subtype).toAffine.Point, (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ (α P)) = α₀ ((WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ P)) :=
  liftable p W hα₀

end S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_comp_reduceHom_of_mem_rationalHomSet (solution)
