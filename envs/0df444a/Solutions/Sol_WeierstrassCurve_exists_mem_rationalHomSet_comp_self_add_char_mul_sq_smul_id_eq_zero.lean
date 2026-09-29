-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e81d21b1-7935-5030-90ce-e25b2655b8c1

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Theorems.Thm_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
import Theorems.Thm_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute
import Theorems.Thm_Rat_exists_ternary_eq_neg_prime_of_forall_padic_isotropic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"
open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ map_map a₁ map map_j mk Affine.Point.some exists_variableChange_of_j_eq ofJ_j Affine.Point.map_injective Affine.Point.some.inj ofJ map_id IsIntegral toAffine map_baseChange Affine.Point mk.inj map_injective Affine.Point.map_zero Affine.Point.map Affine.Point.some_ne_zero VariableChange Affine.Point.map_some Affine.Point.neg_some baseChange j evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet pointAddEquivOfEq pointAddEquivOfEq_some comp_mem_rationalHomSet add_mem_rationalHomSet exists_isDualPair_of_mem_rationalHomSet exists_mem_rationalHomSet_apply_map_eq_map_apply exists_addEquiv_point_variableChange j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero"
namespace SupersingularSqrtNegP
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

end HomSet

section EqTransport

variable {κ : Type*} [Field κ] [DecidableEq κ]

theorem conjEq_mem_rationalHomSet {V V' : WeierstrassCurve κ} (e : V = V')
    {ν : V.toAffine.Point →+ V.toAffine.Point} (hν : ν ∈ rationalHomSet κ V V) :
    ((pointAddEquivOfEq e).toAddMonoidHom.comp
        (ν.comp (pointAddEquivOfEq e).symm.toAddMonoidHom) :
      V'.toAffine.Point →+ V'.toAffine.Point) ∈ rationalHomSet κ V' V' := by
  subst e
  have : (pointAddEquivOfEq (rfl : V = V)).toAddMonoidHom.comp
      (ν.comp (pointAddEquivOfEq (rfl : V = V)).symm.toAddMonoidHom) = ν := by
    ext P; rfl
  rw [this]
  exact hν

end EqTransport

section Additive

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem conj_comp_conj_add_zsmul_id_eq_zero (e : G ≃+ H) (α : G →+ G) (c : ℤ)
    (h : α.comp α + c • AddMonoidHom.id G = 0) :
    (e.toAddMonoidHom.comp (α.comp e.symm.toAddMonoidHom)).comp
        (e.toAddMonoidHom.comp (α.comp e.symm.toAddMonoidHom)) + c • AddMonoidHom.id H = 0 := by
  ext Q
  have h' := DFunLike.congr_fun h (e.symm Q)
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
    AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at h' ⊢
  change e (α (e.symm (e (α (e.symm Q))))) + c • Q = 0
  rw [e.symm_apply_apply]
  have : e (α (α (e.symm Q)) + c • e.symm Q) = e 0 := by rw [h']
  rw [map_add, map_zsmul, e.apply_symm_apply, _root_.map_zero] at this
  exact this

theorem forall_nsmul_eq_zero_of_injective (f : G →+ H) (hf : Function.Injective f) (p : ℕ)
    (hH : ∀ Q : H, p • Q = 0 → Q = 0) : ∀ P : G, p • P = 0 → P = 0 := by
  intro P hP
  apply hf
  rw [_root_.map_zero]
  exact hH _ (by rw [← map_nsmul, hP, _root_.map_zero])

theorem eq_zero_of_prime_smul_of_zsmul {P : G} {r : ℕ} (hr : r.Prime) {N : ℤ} (hN0 : 0 < N)
    (hNr : N < r) (hrP : (r : ℤ) • P = 0) (hNP : N • P = 0) : P = 0 := by
  have hcop : IsCoprime (r : ℤ) N := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd (r : ℤ) N ∣ r := by
      have := Int.gcd_dvd_left (r : ℤ) N
      exact_mod_cast this
    rcases (Nat.dvd_prime hr).mp h1 with h | h
    · exact h
    · exfalso
      have h2 : ((Int.gcd (r : ℤ) N : ℕ) : ℤ) ∣ N := Int.gcd_dvd_right (r : ℤ) N
      rw [h] at h2
      have := Int.le_of_dvd hN0 h2
      omega
  obtain ⟨a, b, hab⟩ := hcop
  calc P = (1 : ℤ) • P := (one_zsmul P).symm
    _ = (a * r + b * N) • P := by rw [hab]
    _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, hrP, hNP, zsmul_zero, zsmul_zero, add_zero]

end Additive

section Descend

variable {κ : Type*} {k : Type*} [Field κ] [Field k] [Algebra κ k] [DecidableEq k]

theorem mem_rationalHomSet_map_of_mem {W₁ W₂ : WeierstrassCurve κ}
    {β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hβ : β ∈ rationalHomSet k W₁ W₂) :
    (β : ((W₁.map (algebraMap κ k)).baseChange k).toAffine.Point →+
        ((W₂.map (algebraMap κ k)).baseChange k).toAffine.Point) ∈
      rationalHomSet k (W₁.map (algebraMap κ k)) (W₂.map (algebraMap κ k)) := by
  rcases hβ with hβ | ⟨nX, dX, nY, dY, B, hB, h⟩
  · exact Or.inl hβ
  · right
    have hev : ∀ (P : κ[X][Y]) (x y : k),
        evalEvalBC (F := k) k (P.map (mapRingHom (algebraMap κ k))) x y = evalEvalBC k P x y := by
      intro P x y
      unfold evalEvalBC
      rw [Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]
    refine ⟨nX.map (mapRingHom (algebraMap κ k)), dX.map (mapRingHom (algebraMap κ k)),
      nY.map (mapRingHom (algebraMap κ k)), dY.map (mapRingHom (algebraMap κ k)), B, hB, ?_⟩
    intro x y hns hx
    obtain ⟨hdX, hdY, h', hP⟩ := h x y hns hx
    refine ⟨by rw [hev]; exact hdX, by rw [hev]; exact hdY, ?_⟩
    simp only [hev]
    exact ⟨h', hP⟩

end Descend

section VarChange

variable {k : Type*} [Field k] [DecidableEq k]

omit [DecidableEq k] in
private theorem exists_eq_some {W : WeierstrassCurve k}
    {P : W.toAffine.Point} {u v u' v' : k}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀)
    (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

theorem addEquiv_mem_rationalHomSet (W : WeierstrassCurve k) (γ : VariableChange k)
    (e : W.toAffine.Point ≃+ (γ • W).toAffine.Point)
    (he : ∀ (x y : k) (h : W.toAffine.Nonsingular x y),
      ∃ h' : (γ • W).toAffine.Nonsingular ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
        ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))),
        e (.some x y h) = .some ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
          ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))) h') :
    (e.toAddMonoidHom : (W.baseChange k).toAffine.Point →+ ((γ • W).baseChange k).toAffine.Point) ∈
      rationalHomSet k W (γ • W) := by
  right
  refine ⟨C (C ((↑γ.u⁻¹ : k) ^ 2) * (X - C γ.r)), 1,
    C (C ((↑γ.u⁻¹ : k) ^ 3)) * (X - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))), 1, ∅,
    Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC (F := k) k (1 : k[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := k) k (C (C ((↑γ.u⁻¹ : k) ^ 2) * (X - C γ.r)) : k[X][Y]) x y =
      (↑γ.u⁻¹ : k) ^ 2 * (x - γ.r) := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := k) k
      (C (C ((↑γ.u⁻¹ : k) ^ 3)) * (X - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))) : k[X][Y]) x y =
      (↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t)) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  obtain ⟨h', hP⟩ := he x y h
  exact exists_eq_some hP (by rw [e0, e1, div_one]) (by rw [e0, e2, div_one])

theorem addEquiv_symm_mem_rationalHomSet (W : WeierstrassCurve k) (γ : VariableChange k)
    (e : W.toAffine.Point ≃+ (γ • W).toAffine.Point)
    (he : ∀ (x y : k) (h : W.toAffine.Nonsingular x y),
      ∃ h' : (γ • W).toAffine.Nonsingular ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
        ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))),
        e (.some x y h) = .some ((↑γ.u⁻¹ : k) ^ 2 * (x - γ.r))
          ((↑γ.u⁻¹ : k) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t))) h') :
    (e.symm.toAddMonoidHom :
        ((γ • W).baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k (γ • W) W := by
  right
  refine ⟨C (C ((γ.u : k) ^ 2) * X + C γ.r), 1,
    C (C ((γ.u : k) ^ 3)) * X + C (C ((γ.u : k) ^ 2 * γ.s) * X + C γ.t), 1, ∅,
    Set.finite_empty, fun x' y' h' _ => ?_⟩
  have e0 : evalEvalBC (F := k) k (1 : k[X][Y]) x' y' = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := k) k (C (C ((γ.u : k) ^ 2) * X + C γ.r) : k[X][Y]) x' y' =
      (γ.u : k) ^ 2 * x' + γ.r := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := k) k
      (C (C ((γ.u : k) ^ 3)) * X + C (C ((γ.u : k) ^ 2 * γ.s) * X + C γ.t) : k[X][Y]) x' y' =
      (γ.u : k) ^ 3 * y' + ((γ.u : k) ^ 2 * γ.s * x' + γ.t) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩

  set P := e.symm (.some x' y' h') with hPdef
  have hP0 : P ≠ 0 := by
    intro h0
    have : e P = e 0 := by rw [h0]
    rw [hPdef, AddEquiv.apply_symm_apply, _root_.map_zero] at this
    exact Affine.Point.some_ne_zero _ this
  rcases hPxy : P with _ | ⟨x, y, h⟩
  · exact absurd hPxy hP0
  · obtain ⟨h'', hexy⟩ := he x y h
    have key : e (.some x y h) = .some x' y' h' := by
      rw [← hPxy, hPdef, AddEquiv.apply_symm_apply]
    rw [hexy] at key
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj key
    have hw : (↑γ.u⁻¹ : k) = (γ.u : k)⁻¹ := Units.val_inv_eq_inv_val γ.u
    have hu0 : (γ.u : k) ≠ 0 := γ.u.ne_zero
    have hPe : e.symm.toAddMonoidHom (.some x' y' h') = .some x y h := by
      show e.symm (.some x' y' h') = .some x y h
      rw [← hPdef]; exact hPxy
    refine exists_eq_some hPe ?_ ?_
    · rw [e0, e1, div_one, ← hx, hw]
      field_simp
      ring
    · rw [e0, e2, div_one, ← hx, ← hy, hw]
      field_simp
      ring

end VarChange

section FiniteFields

variable {F₁ : Type*} [Field F₁] {k₀ : Type*} [Field k₀] [Algebra F₁ k₀]

theorem exists_frobenius_algHom (p : ℕ) [Fact p.Prime] [Fintype F₁] [CharP F₁ p] [CharP k₀ p] :
    ∃ σ : k₀ →ₐ[F₁] k₀, ∀ x, σ x = x ^ Fintype.card F₁ := by
  obtain ⟨⟨d, hd⟩, hp, hcard⟩ := FiniteField.card F₁ p
  have hcard' : Fintype.card F₁ = p ^ d := hcard
  refine ⟨{ toRingHom := iterateFrobenius k₀ p d, commutes' := fun c => ?_ }, fun x => ?_⟩
  · show (algebraMap F₁ k₀ c) ^ p ^ d = algebraMap F₁ k₀ c
    rw [← map_pow, ← hcard', FiniteField.pow_card]
  · show x ^ p ^ d = _
    rw [hcard']

def fixedFieldOf (τ : k₀ →ₐ[F₁] k₀) : IntermediateField F₁ k₀ :=
  (AlgHom.equalizer τ (AlgHom.id F₁ k₀)).toIntermediateField fun x hx => by
    rw [AlgHom.mem_equalizer, AlgHom.id_apply] at hx ⊢
    rw [map_inv₀, hx]

theorem mem_fixedFieldOf {τ : k₀ →ₐ[F₁] k₀} {x : k₀} : x ∈ fixedFieldOf τ ↔ τ x = x := by
  show x ∈ (AlgHom.equalizer τ (AlgHom.id F₁ k₀)) ↔ _
  rw [AlgHom.mem_equalizer, AlgHom.id_apply]

theorem finite_fixedFieldOf_and_natCard (p : ℕ) [Fact p.Prime] [CharP k₀ p] [IsAlgClosed k₀]
    (τ : k₀ →ₐ[F₁] k₀) {N : ℕ} (hN : 1 < N) (hpN : p ∣ N) (hτ : ∀ x, τ x = x ^ N) :
    Finite (fixedFieldOf τ) ∧ Nat.card (fixedFieldOf τ) = N := by
  set f : k₀[X] := X ^ N - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k₀ hN
  have hmem : ∀ x : k₀, x ∈ fixedFieldOf τ ↔ x ∈ f.rootSet k₀ := by
    intro x
    rw [mem_fixedFieldOf, hτ, Polynomial.mem_rootSet, Polynomial.aeval_def, Polynomial.eval₂_sub,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, sub_eq_zero]
    exact ⟨fun h => ⟨hf0, h⟩, fun h => h.2⟩
  let eqv : (fixedFieldOf τ) ≃ f.rootSet k₀ := Equiv.subtypeEquivRight hmem
  have hfin : Finite (f.rootSet k₀) := (Polynomial.rootSet_finite f k₀).to_subtype
  refine ⟨Finite.of_equiv _ eqv.symm, ?_⟩
  rw [Nat.card_congr eqv, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree (galois_poly_separable p N hpN) (IsAlgClosed.splits _)]
  exact FiniteField.X_pow_card_sub_X_natDegree_eq k₀ hN

end FiniteFields

section Frobenius

variable {F₁ : Type*} [Field F₁] {k₀ : Type*} [Field k₀] [Algebra F₁ k₀] [DecidableEq k₀]

omit [DecidableEq k₀] in
private theorem some_eq_some {V : WeierstrassCurve k₀} {a b a' b' : k₀}
    {h : V.toAffine.Nonsingular a b} {h' : V.toAffine.Nonsingular a' b'} (ha : a = a') (hb : b = b') :
    Affine.Point.some a b h = Affine.Point.some a' b' h' := by
  subst ha hb; rfl

omit [DecidableEq k₀] in
private theorem exists_some_eq_some {V : WeierstrassCurve k₀} {a b a' b' : k₀}
    (h : V.toAffine.Nonsingular a b) (ha : a = a') (hb : b = b') :
    ∃ h', Affine.Point.some a b h = Affine.Point.some a' b' h' := by
  subst ha hb; exact ⟨h, rfl⟩

theorem iterate_map_some (W : WeierstrassCurve F₁) (σ : k₀ →ₐ[F₁] k₀) (m : ℕ) (x y : k₀)
    (h : (W⁄k₀).toAffine.Nonsingular x y) :
    ∃ h', (Affine.Point.map (W' := W) σ)^[m] (.some x y h) = .some (σ^[m] x) (σ^[m] y) h' := by
  induction m with
  | zero => exact ⟨h, rfl⟩
  | succ m ih =>
    obtain ⟨h', e⟩ := ih
    rw [Function.iterate_succ_apply' (Affine.Point.map (W' := W) σ) m, e, Affine.Point.map_some]
    exact exists_some_eq_some _ (Function.iterate_succ_apply' σ m x).symm
      (Function.iterate_succ_apply' σ m y).symm

theorem iterate_map_zero (W : WeierstrassCurve F₁) (σ : k₀ →ₐ[F₁] k₀) (m : ℕ) :
    (Affine.Point.map (W' := W) σ)^[m] (0 : (W⁄k₀).Point) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih]; rfl

end Frobenius

section Quaternion

variable {A : Type*} [AddCommGroup A]

theorem quaternion_sq_apply (i j : A →+ A) (u v : ℤ) (hi : ∀ a, i (i a) = u • a)
    (hj : ∀ a, j (j a) = v • a) (hij : ∀ a, i (j a) = -(j (i a))) (a b c : ℤ) (P : A) :
    (a • i + b • j + c • i.comp j) ((a • i + b • j + c • i.comp j) P) =
      (a ^ 2 * u + b ^ 2 * v - c ^ 2 * u * v) • P := by
  have hji : ∀ a, j (i a) = -(i (j a)) := fun a => by rw [hij, neg_neg]
  simp only [AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, AddMonoidHom.comp_apply, map_add,
    map_zsmul, map_neg, hi, hj, hji, smul_neg]
  module

end Quaternion

section Denominators

theorem exists_int_of_rat_ternary (u v : ℤ) (p : ℕ) (x y z : ℚ)
    (h : (u : ℚ) * x ^ 2 + (v : ℚ) * y ^ 2 - (u : ℚ) * (v : ℚ) * z ^ 2 = -(p : ℚ)) :
    ∃ a b c D : ℤ, D ≠ 0 ∧ a ^ 2 * u + b ^ 2 * v - c ^ 2 * u * v = -((p : ℤ) * D ^ 2) := by
  refine ⟨x.num * y.den * z.den, y.num * x.den * z.den, z.num * x.den * y.den,
    (x.den : ℤ) * y.den * z.den, ?_, ?_⟩
  · have hx := x.den_pos; have hy := y.den_pos; have hz := z.den_pos
    positivity
  · have hx : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
    have hy : (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
    have hz : (z.num : ℚ) = z * z.den := (Rat.mul_den_eq_num z).symm
    have key : (((x.num * y.den * z.den) ^ 2 * u + (y.num * x.den * z.den) ^ 2 * v -
        (z.num * x.den * y.den) ^ 2 * u * v : ℤ) : ℚ) =
        ((-((p : ℤ) * ((x.den : ℤ) * y.den * z.den) ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [hx, hy, hz]
      linear_combination ((x.den : ℚ) * y.den * z.den) ^ 2 * h
    exact_mod_cast key

end Denominators

section ScalarFrobenius

variable {F₁ : Type*} [Field F₁] [Fintype F₁] {k₀ : Type*} [Field k₀] [DecidableEq k₀] [Algebra F₁ k₀]
  [IsAlgClosed k₀] [Algebra.IsAlgebraic F₁ k₀]

set_option maxHeartbeats 3200000 in

theorem exists_intermediateField_frobenius_eq_smul (p : ℕ) [Fact p.Prime] [CharP F₁ p] [CharP k₀ p]
    (W₁ : WeierstrassCurve F₁) [W₁.IsElliptic] (h : ∀ P : (W₁⁄k₀).Point, p • P = 0 → P = 0) :
    ∃ (E : IntermediateField F₁ k₀) (_ : Fintype E) (σ₂ : k₀ →ₐ[E] k₀) (a : ℤ),
      (∀ x, σ₂ x = x ^ Fintype.card E) ∧
      ∀ P : ((W₁⁄E)⁄k₀).Point, Affine.Point.map (W' := W₁⁄E) σ₂ P = a • P := by

  obtain ⟨σ, hσ⟩ := exists_frobenius_algHom (F₁ := F₁) (k₀ := k₀) p
  obtain ⟨n, hn, a, ha⟩ :=
    WeierstrassCurve.exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero k₀ p W₁ σ hσ h

  obtain ⟨⟨d, hd⟩, -, hcard⟩ := FiniteField.card F₁ p
  have hcard' : Fintype.card F₁ = p ^ d := hcard
  have hq1 : 1 < Fintype.card F₁ := Fintype.one_lt_card
  have hσiter : ∀ (m : ℕ) (x : k₀), σ^[m] x = x ^ Fintype.card F₁ ^ m := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih => intro x; rw [Function.iterate_succ_apply', ih, hσ, ← pow_mul, ← pow_succ]
  have hσn : ∀ x : k₀, (σ ^ n) x = x ^ Fintype.card F₁ ^ n := fun x => by
    rw [AlgHom.coe_pow]; exact hσiter n x
  have hqn1 : 1 < Fintype.card F₁ ^ n := Nat.one_lt_pow hn.ne' hq1
  have hpqn : p ∣ Fintype.card F₁ ^ n := by
    rw [hcard', ← pow_mul]
    exact dvd_pow_self p (Nat.mul_ne_zero hd.ne' hn.ne')
  obtain ⟨hEfin, hEcard⟩ := finite_fixedFieldOf_and_natCard p (σ ^ n) hqn1 hpqn hσn
  haveI : Finite (fixedFieldOf (σ ^ n)) := hEfin
  letI instE : Fintype (fixedFieldOf (σ ^ n)) := Fintype.ofFinite _
  have hEcard' : Fintype.card (fixedFieldOf (σ ^ n)) = Fintype.card F₁ ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hEcard

  let σ₂ : k₀ →ₐ[fixedFieldOf (σ ^ n)] k₀ :=
    { toRingHom := (σ ^ n).toRingHom
      commutes' := fun c => mem_fixedFieldOf.mp c.2 }
  have hσ₂ : ∀ x : k₀, σ₂ x = (σ ^ n) x := fun x => rfl
  have hW₂₁ : (W₁⁄(fixedFieldOf (σ ^ n)))⁄k₀ = W₁⁄k₀ :=
    W₁.map_baseChange (IsScalarTower.toAlgHom F₁ (fixedFieldOf (σ ^ n)) k₀)
  refine ⟨fixedFieldOf (σ ^ n), instE, σ₂, a, fun x => by rw [hEcard', hσ₂, hσn], ?_⟩

  have key : ∀ P : ((W₁⁄(fixedFieldOf (σ ^ n)))⁄k₀).Point,
      pointAddEquivOfEq hW₂₁ (Affine.Point.map (W' := W₁⁄(fixedFieldOf (σ ^ n))) σ₂ P) =
        (Affine.Point.map (W' := W₁) σ)^[n] (pointAddEquivOfEq hW₂₁ P) := by
    rintro (_ | ⟨x, y, hxy⟩)
    · show pointAddEquivOfEq hW₂₁ (Affine.Point.map (W' := W₁⁄(fixedFieldOf (σ ^ n))) σ₂ 0) =
        (Affine.Point.map (W' := W₁) σ)^[n] (pointAddEquivOfEq hW₂₁ 0)
      rw [Affine.Point.map_zero, _root_.map_zero, iterate_map_zero]
    · rw [Affine.Point.map_some, pointAddEquivOfEq_some, pointAddEquivOfEq_some]
      obtain ⟨h', e⟩ := iterate_map_some W₁ σ n x y (hW₂₁ ▸ hxy)
      rw [e]
      exact some_eq_some (by rw [hσ₂, AlgHom.coe_pow]) (by rw [hσ₂, AlgHom.coe_pow])
  intro P
  apply (pointAddEquivOfEq hW₂₁).injective
  rw [key, ha, map_zsmul]

end ScalarFrobenius

section OverFiniteField

variable {E : Type*} [Field E] [Fintype E] {k₀ : Type*} [Field k₀] [DecidableEq k₀] [Algebra E k₀]
  [IsAlgClosed k₀] [Algebra.IsAlgebraic E k₀]
  {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] [Algebra E k] [Algebra k₀ k] [IsScalarTower E k₀ k]

set_option maxHeartbeats 3200000 in

theorem exists_mem_rationalHomSet_comp_self_add_smul_eq_zero (p : ℕ) [Fact p.Prime] [CharP k₀ p]
    (W₂ : WeierstrassCurve E) [W₂.IsElliptic] (σ₂ : k₀ →ₐ[E] k₀) (hσ₂ : ∀ x, σ₂ x = x ^ Fintype.card E)
    (a : ℤ) (ha₂ : ∀ P : (W₂⁄k₀).Point, Affine.Point.map (W' := W₂) σ₂ P = a • P) :
    ∃ α ∈ rationalHomSet k W₂ W₂, ∃ D : ℤ, D ≠ 0 ∧
      α.comp α + ((p : ℤ) * D ^ 2) • AddMonoidHom.id _ = 0 := by
  have hp : Fact p.Prime := inferInstance
  haveI : (W₂⁄k₀).IsElliptic := (inferInstance : (W₂.map (algebraMap E k₀)).IsElliptic)
  haveI : (W₂⁄k).IsElliptic := (inferInstance : (W₂.map (algebraMap E k)).IsElliptic)

  obtain ⟨i, hi, j, hj, u, v, hu, hv, hii, hjj, hij⟩ :=
    WeierstrassCurve.exists_anticommuting_pair_mem_rationalHomSet_of_frobenius_eq_smul k₀ W₂ σ₂ hσ₂ a ha₂

  have hloc : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∃ z x y : ℚ_[ℓ], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - ((u : ℚ) : ℚ_[ℓ]) * x ^ 2 - ((v : ℚ) : ℚ_[ℓ]) * y ^ 2 = 0 := by
    intro ℓ hℓ hℓp
    have hℓk : ∀ m : ℕ, ((ℓ ^ m : ℕ) : k₀) ≠ 0 := by
      intro m
      rw [Nat.cast_pow]
      refine pow_ne_zero _ fun h0 => hℓp ?_
      rw [CharP.cast_eq_zero_iff k₀ p] at h0
      exact ((Nat.prime_dvd_prime_iff_eq hp.out hℓ.out).mp h0).symm
    have hA : ∀ m : ℕ, Nonempty (ZMod (ℓ ^ m) × ZMod (ℓ ^ m) ≃+
        Submodule.torsionBy ℤ (W₂⁄k₀).Point ((ℓ ^ m : ℕ) : ℤ)) := fun m =>
      WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed W₂ (hℓk m)
    obtain ⟨z, x, y, hne, hzxy⟩ :=
      Padic.exists_ternary_isotropic_of_sq_eq_smul_of_anticommute ℓ hA u v i j hii hjj hij
    exact ⟨z, x, y, hne, by simpa using hzxy⟩

  obtain ⟨x, y, z, hxyz⟩ := Rat.exists_ternary_eq_neg_prime_of_forall_padic_isotropic p (u : ℚ) (v : ℚ)
    (Int.cast_ne_zero.mpr hu) (Int.cast_ne_zero.mpr hv) hloc
  obtain ⟨X', Y', Z', D, hD, hXYZ⟩ := exists_int_of_rat_ternary u v p x y z hxyz

  set α₀ : (W₂⁄k₀).Point →+ (W₂⁄k₀).Point := X' • i + Y' • j + Z' • i.comp j with hα₀
  have hα₀mem : α₀ ∈ rationalHomSet k₀ W₂ W₂ :=
    WeierstrassCurve.add_mem_rationalHomSet k₀ W₂ W₂
      (WeierstrassCurve.add_mem_rationalHomSet k₀ W₂ W₂ (zsmul_mem_rationalHomSet hi X')
        (zsmul_mem_rationalHomSet hj Y'))
      (zsmul_mem_rationalHomSet (WeierstrassCurve.comp_mem_rationalHomSet k₀ W₂ W₂ W₂ hj hi) Z')
  have hα₀sq : ∀ P, α₀ (α₀ P) + ((p : ℤ) * D ^ 2) • P = 0 := by
    intro P
    rw [hα₀, quaternion_sq_apply i j u v hii hjj hij X' Y' Z' P, hXYZ, neg_zsmul, neg_add_cancel]

  obtain ⟨α, hα, hαα₀⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply k₀ k W₂ W₂ hα₀mem
  set ι₂ : k₀ →ₐ[E] k := IsScalarTower.toAlgHom E k₀ k with hι₂
  set γ : (W₂⁄k).Point →+ (W₂⁄k).Point := α.comp α + ((p : ℤ) * D ^ 2) • AddMonoidHom.id _ with hγ
  have hγmem : γ ∈ rationalHomSet k W₂ W₂ :=
    WeierstrassCurve.add_mem_rationalHomSet k W₂ W₂ (WeierstrassCurve.comp_mem_rationalHomSet k W₂ W₂ W₂ hα hα)
      (zsmul_mem_rationalHomSet (id_mem_rationalHomSet k W₂) _)
  have hγι : ∀ P, γ (Affine.Point.map (W' := W₂) ι₂ P) = 0 := by
    intro P
    simp only [hγ, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
      AddMonoidHom.id_apply]
    rw [hαα₀, hαα₀, ← map_zsmul, ← map_add, hα₀sq, _root_.map_zero]
  have hγ0 : γ = 0 := by
    by_contra hne
    obtain ⟨τ, -, N, hN, hdual⟩ :=
      WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet k W₂ W₂ hγmem hne

    obtain ⟨r, hrge, hr⟩ := Nat.exists_infinite_primes (N.toNat + p + 1)
    have hrp : r ≠ p := by omega
    have hrN : N < r := by omega
    have hrk : (r : k₀) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff k₀ p] at h0
      exact hrp ((Nat.prime_dvd_prime_iff_eq hp.out hr).mp h0).symm
    obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed W₂ hrk
    haveI : Nontrivial (ZMod r) := ZMod.nontrivial_iff.mpr hr.one_lt.ne'
    set P₀ : (W₂⁄k₀).Point := ((e (1, 0) : Submodule.torsionBy ℤ (W₂⁄k₀).Point r) : (W₂⁄k₀).Point)
      with hP₀
    have hP₀r : (r : ℤ) • P₀ = 0 := (Submodule.mem_torsionBy_iff _ _).mp (e (1, 0)).2
    have hP₀ne : P₀ ≠ 0 := by
      intro h0
      have h1 : e (1, 0) = 0 := Subtype.ext h0
      have h2 : ((1, 0) : ZMod r × ZMod r) = 0 := e.injective (by rw [h1, _root_.map_zero])
      exact one_ne_zero (Prod.mk.inj h2).1
    have hNP₀ : N • P₀ = 0 := by
      apply Affine.Point.map_injective (W' := W₂) ι₂
      rw [map_zsmul, _root_.map_zero, ← hdual.comp_left (Affine.Point.map (W' := W₂) ι₂ P₀), hγι,
        _root_.map_zero]
    exact hP₀ne (eq_zero_of_prime_smul_of_zsmul hr hN hrN hP₀r hNP₀)
  exact ⟨α, hα, D, hD, hγ0⟩

end OverFiniteField

section Assembly

variable {F₁ : Type*} [Field F₁] [Fintype F₁] {k₀ : Type*} [Field k₀] [DecidableEq k₀] [Algebra F₁ k₀]
  [IsAlgClosed k₀] [Algebra.IsAlgebraic F₁ k₀]
  {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k] [Algebra F₁ k] [Algebra k₀ k]
  [IsScalarTower F₁ k₀ k]

set_option maxHeartbeats 3200000 in

theorem exists_of_finite_model (p : ℕ) [Fact p.Prime] [CharP F₁ p] [CharP k₀ p]
    (W₁ : WeierstrassCurve F₁) [W₁.IsElliptic] (X : WeierstrassCurve k) (C : VariableChange k)
    (hCX : C • (W₁⁄k) = X) (h : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    ∃ α ∈ WeierstrassCurve.rationalHomSet k X X, ∃ m : ℤ, m ≠ 0 ∧
      α.comp α + ((p : ℤ) * m ^ 2) • AddMonoidHom.id _ = 0 := by
  haveI : (W₁⁄k).IsElliptic := (inferInstance : (W₁.map (algebraMap F₁ k)).IsElliptic)
  haveI : (W₁⁄k₀).IsElliptic := (inferInstance : (W₁.map (algebraMap F₁ k₀)).IsElliptic)
  obtain ⟨eC, heC⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange (W₁⁄k) C

  let ι : k₀ →ₐ[F₁] k := IsScalarTower.toAlgHom F₁ k₀ k
  have hW₁ss : ∀ P : (W₁⁄k₀).Point, p • P = 0 → P = 0 :=
    forall_nsmul_eq_zero_of_injective
      ((pointAddEquivOfEq hCX).toAddMonoidHom.comp
        (eC.toAddMonoidHom.comp (Affine.Point.map (W' := W₁) ι)))
      ((pointAddEquivOfEq hCX).injective.comp
        (eC.injective.comp (Affine.Point.map_injective (W' := W₁) ι))) p h

  obtain ⟨E, instE, σ₂, a, hσ₂, ha₂⟩ := exists_intermediateField_frobenius_eq_smul p W₁ hW₁ss
  letI : Fintype E := instE
  haveI : Algebra.IsAlgebraic E k₀ := Algebra.IsAlgebraic.tower_top (K := F₁) E
  haveI : (W₁⁄E).IsElliptic := (inferInstance : (W₁.map (algebraMap F₁ E)).IsElliptic)
  obtain ⟨α, hα, D, hD, hαsq⟩ :=
    exists_mem_rationalHomSet_comp_self_add_smul_eq_zero (k := k) p (W₁⁄E) σ₂ hσ₂ a ha₂

  have hαk := mem_rationalHomSet_map_of_mem hα
  have hW₂k : (W₁⁄E)⁄k = W₁⁄k := by
    show (W₁.map (algebraMap F₁ E)).map (algebraMap E k) = W₁.map (algebraMap F₁ k)
    rw [WeierstrassCurve.map_map]
    congr 1
    ext c
    show algebraMap k₀ k (algebraMap E k₀ (algebraMap F₁ E c)) = algebraMap F₁ k c
    rw [← IsScalarTower.algebraMap_apply F₁ E k₀, ← IsScalarTower.algebraMap_apply F₁ k₀ k]
  set α₁ : (W₁⁄k).toAffine.Point →+ (W₁⁄k).toAffine.Point :=
    (pointAddEquivOfEq hW₂k).toAddMonoidHom.comp (α.comp (pointAddEquivOfEq hW₂k).symm.toAddMonoidHom)
    with hα₁
  have hα₁mem : α₁ ∈ rationalHomSet k (W₁⁄k) (W₁⁄k) := conjEq_mem_rationalHomSet hW₂k hαk
  have hα₁sq : α₁.comp α₁ + ((p : ℤ) * D ^ 2) • AddMonoidHom.id _ = 0 :=
    conj_comp_conj_add_zsmul_id_eq_zero _ α _ hαsq
  set α₂ : (C • W₁⁄k).toAffine.Point →+ (C • W₁⁄k).toAffine.Point :=
    eC.toAddMonoidHom.comp (α₁.comp eC.symm.toAddMonoidHom) with hα₂
  have hα₂mem : α₂ ∈ rationalHomSet k (C • W₁⁄k) (C • W₁⁄k) :=
    WeierstrassCurve.comp_mem_rationalHomSet k _ _ _
      (WeierstrassCurve.comp_mem_rationalHomSet k _ _ _
        (addEquiv_symm_mem_rationalHomSet (W₁⁄k) C eC heC) hα₁mem)
      (addEquiv_mem_rationalHomSet (W₁⁄k) C eC heC)
  have hα₂sq : α₂.comp α₂ + ((p : ℤ) * D ^ 2) • AddMonoidHom.id _ = 0 :=
    conj_comp_conj_add_zsmul_id_eq_zero eC α₁ _ hα₁sq
  refine ⟨(pointAddEquivOfEq hCX).toAddMonoidHom.comp (α₂.comp (pointAddEquivOfEq hCX).symm.toAddMonoidHom),
    conjEq_mem_rationalHomSet hCX hα₂mem, D, hD, ?_⟩
  exact conj_comp_conj_add_zsmul_id_eq_zero _ α₂ _ hα₂sq

end Assembly

end WeierstrassCurve.SupersingularSqrtNegP

open WeierstrassCurve.SupersingularSqrtNegP in
set_option maxHeartbeats 3200000 in
theorem solution {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (X : WeierstrassCurve k) [X.IsElliptic] (h : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) : ∃ α ∈ WeierstrassCurve.rationalHomSet k X X, ∃ m : ℤ, m ≠ 0 ∧ α.comp α + ((p : ℤ) * m ^ 2) • AddMonoidHom.id _ = 0 := by
  have hp : Fact p.Prime := inferInstance
  letI : Algebra (ZMod p) k := ZMod.algebra k p

  have hp2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
  have h' : ∀ P : X.toAffine.Point, (p : ℤ) • P = 0 → P = 0 :=
    fun P hP => h P (by rwa [natCast_zsmul] at hP)
  have hjint : IsIntegral (ZMod p) X.j := by
    refine ⟨Polynomial.X ^ (p ^ 2) - Polynomial.X,
      Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp2), ?_⟩
    simp [WeierstrassCurve.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero p X h']

  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : IntermediateField (ZMod p) k, F₁ = IntermediateField.adjoin (ZMod p) {X.j} :=
    ⟨_, rfl⟩
  haveI : FiniteDimensional (ZMod p) F₁ := by
    rw [hF₁]; exact IntermediateField.adjoin.finiteDimensional hjint
  haveI : Finite F₁ := Module.finite_of_finite (ZMod p)
  letI : Fintype F₁ := Fintype.ofFinite F₁
  haveI : CharP F₁ p := charP_of_injective_algebraMap (algebraMap (ZMod p) F₁).injective p
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : IntermediateField F₁ k, k₀ = algebraicClosure F₁ k := ⟨_, rfl⟩
  haveI : IsAlgClosed k₀ := by rw [hk₀]; exact (algebraicClosure.isAlgClosure F₁ k).isAlgClosed
  haveI : Algebra.IsAlgebraic F₁ k₀ := by rw [hk₀]; infer_instance
  haveI : CharP k₀ p := charP_of_injective_algebraMap (algebraMap F₁ k₀).injective p

  have hjmem : X.j ∈ F₁ := by rw [hF₁]; exact IntermediateField.mem_adjoin_simple_self (ZMod p) X.j
  haveI : ((WeierstrassCurve.ofJ (⟨X.j, hjmem⟩ : F₁))⁄k).IsElliptic :=
    (inferInstance : ((WeierstrassCurve.ofJ (⟨X.j, hjmem⟩ : F₁)).map (algebraMap F₁ k)).IsElliptic)
  have hjW₁ : ((WeierstrassCurve.ofJ (⟨X.j, hjmem⟩ : F₁))⁄k).j = X.j := by
    show ((WeierstrassCurve.ofJ (⟨X.j, hjmem⟩ : F₁)).map (algebraMap F₁ k)).j = X.j
    rw [WeierstrassCurve.map_j, WeierstrassCurve.ofJ_j]
    rfl
  obtain ⟨C, hCX⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ X hjW₁
  exact exists_of_finite_model (k₀ := k₀) p (WeierstrassCurve.ofJ (⟨X.j, hjmem⟩ : F₁)) X C hCX h

end S_WeierstrassCurve_exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero (solution)
