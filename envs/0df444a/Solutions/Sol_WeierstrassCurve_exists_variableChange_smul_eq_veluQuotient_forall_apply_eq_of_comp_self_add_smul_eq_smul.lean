-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8435d804-3467-5105-8f3f-57bf9f07b3ce

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_addOrderOf_eq_two_mul_add_one
import Theorems.Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed

import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply"
p2m_attr_erase "simp" "ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map toAffine Affine.Point VariableChange Affine.Point.neg_some baseChange evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet veluQuotient veluX veluY oddOrderSummingSet isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero surjective_of_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet card_torsion_of_isAlgClosed Affine.Point.equivOfVariableChangeEq exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id"
namespace KernelIsoVC
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
    exact hR (by
      have h := DFunLike.congr_fun h0 R
      first
        | simpa using h
        | (simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at h; exact h)
        | exact h)
  obtain ⟨P', hP'⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hmem hne P
  exact ⟨P', by first | exact hP' | simpa using hP'⟩

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

section Units

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
variable {V : WeierstrassCurve k} [V.IsElliptic]
variable {φ₀ : W.toAffine.Point →+ V.toAffine.Point} (hφ₀ : φ₀ ∈ rationalHomSet k W V)
variable {m : ℕ} (hm : (m : k) ≠ 0)

include hφ₀ hm in

theorem exists_inverse {ι : V.toAffine.Point →+ W.toAffine.Point} (hι : ι ∈ rationalHomSet k V W)
    (hinj : Function.Injective ι)
    {γ' : W.toAffine.Point →+ W.toAffine.Point} (hγ' : γ' ∈ rationalHomSet k W W)
    (hγγ' : ∀ P, ι (φ₀ (γ' P)) = (m : ℤ) • P)
    (hkill : ∀ T : W.toAffine.Point, (m : ℤ) • T = 0 → φ₀ (γ' T) = 0) :
    ∃ τ : W.toAffine.Point →+ V.toAffine.Point, τ ∈ rationalHomSet k W V ∧
      ι.comp τ = AddMonoidHom.id W.toAffine.Point ∧ τ.comp ι = AddMonoidHom.id V.toAffine.Point := by
  have hm0 : (m : ℤ) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; exact hm (by simp)
    exact_mod_cast this

  have hθ : φ₀.comp γ' ∈ rationalHomSet k W V :=
    WeierstrassCurve.comp_mem_rationalHomSet k W W V hγ' hφ₀
  have hkill' : ∀ P : (W.baseChange k).toAffine.Point, (m : ℤ) • P = 0 → (φ₀.comp γ') P = 0 :=
    fun T hT => hkill T hT
  obtain ⟨τ, hτ, hθτ⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
    k W V hm hθ hkill'
  let τ₀ : W.toAffine.Point →+ V.toAffine.Point := τ
  have hθτ' : ∀ P : W.toAffine.Point, φ₀ (γ' P) = (m : ℤ) • τ₀ P := fun P => hθτ P

  have hιτ : ι.comp τ₀ = AddMonoidHom.id _ := by
    have hδ := eq_zero_of_zsmul_apply_eq_zero W hm0 (ι.comp τ₀ - AddMonoidHom.id _) (fun P => by
      show (m : ℤ) • (ι (τ₀ P) - P) = 0
      rw [smul_sub, ← map_zsmul, ← hθτ' P, hγγ', sub_self])
    exact sub_eq_zero.mp hδ
  refine ⟨τ₀, hτ, hιτ, ?_⟩
  ext P
  apply hinj
  exact DFunLike.congr_fun hιτ (ι P)

end Units

section Main

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

theorem main {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ rationalHomSet k W W)
    (s : ℤ) (n : ℕ)
    (hchar : β.comp β + ((2 * n + 1 : ℕ) : ℤ) • AddMonoidHom.id _ = s • β)
    (hirr : ∀ x : ℤ, x ^ 2 - s * x + (2 * n + 1 : ℕ) ≠ 0)
    (hprim : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ s → ¬ (ℓ : ℤ) ^ 2 ∣ ((2 * n + 1 : ℕ) : ℤ))
    (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1) (hQ₀β : β Q₀ = 0)
    (φ₀ : W.toAffine.Point →+ (W.veluQuotient (W.oddOrderSummingSet Q₀ n)).toAffine.Point)
    (hφ₀ker : φ₀.ker = AddSubgroup.zmultiples Q₀)
    (hφ₀ : ∀ (x y : k) (h : W.toAffine.Nonsingular x y),
      (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        ∃ h', φ₀ (.some x y h) = .some (W.veluX (W.oddOrderSummingSet Q₀ n) x)
          (W.veluY (W.oddOrderSummingSet Q₀ n) x y) h') :
    ∃ (γ₀ : VariableChange k) (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n)),
      ∀ P, β P = Affine.Point.equivOfVariableChangeEq hγ₀ (φ₀ P) := by
  set m : ℕ := 2 * n + 1 with hmdef
  have hn0 : m ≠ 0 := by omega
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hn0

  obtain ⟨-, hcardβ⟩ :=
    W.isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul hβ s m hchar hm hirr hprim
  haveI hfinβ : Finite β.ker := Nat.finite_of_card_ne_zero (by rw [hcardβ]; exact hn0)
  have hkerβ : β.ker = AddSubgroup.zmultiples Q₀ := by
    symm
    refine AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr hQ₀β) ?_
    rw [hcardβ, Nat.card_zmultiples, hQ₀]

  haveI : (W.veluQuotient (W.oddOrderSummingSet Q₀ n)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr
      (veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq W n Q₀ hQ₀)⟩
  obtain ⟨hφ₀rat, hfactor⟩ :=
    W.veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq n Q₀ hQ₀ φ₀ hφ₀ker hφ₀
  obtain ⟨ι₀', hι₀, hβfac'⟩ := hfactor W β hβ hQ₀β
  let ι₀ : (W.veluQuotient (W.oddOrderSummingSet Q₀ n)).toAffine.Point →+ W.toAffine.Point := ι₀'
  have hβfac : β = ι₀.comp φ₀ := hβfac'
  have hkerφ₀ : φ₀.ker = β.ker := by rw [hφ₀ker, hkerβ]

  have hφ₀ne : φ₀ ≠ 0 := by
    intro h0
    obtain ⟨P, hP⟩ := exists_zsmul_ne_zero W hm0
    have hPker : P ∈ β.ker := by
      rw [← hkerφ₀, h0]; exact AddMonoidHom.mem_ker.mpr rfl
    apply hP
    have h1 : m • (⟨P, hPker⟩ : β.ker) = 0 := by rw [← hcardβ]; exact card_nsmul_eq_zero'
    have h2 := congrArg Subtype.val h1
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at h2
    rw [natCast_zsmul]
    exact h2
  have hφ₀surj : Function.Surjective φ₀ :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k hφ₀rat hφ₀ne
  have hι₀inj : Function.Injective ι₀ := by
    intro P₁ P₂ h12
    obtain ⟨P, rfl⟩ := hφ₀surj P₁
    obtain ⟨R, rfl⟩ := hφ₀surj P₂
    have h1 : β (P - R) = 0 := by rw [hβfac, map_sub]; exact sub_eq_zero.mpr h12
    have h2 : P - R ∈ φ₀.ker := by rw [hkerφ₀]; exact h1
    rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at h2
    rw [h2]

  let β' : W.toAffine.Point →+ W.toAffine.Point := s • AddMonoidHom.id _ - β
  have hβ'rat : β' ∈ rationalHomSet k W W :=
    sub_mem_rationalHomSet (zsmul_id_mem_rationalHomSet W s) hβ
  have hββ' : ∀ P, ι₀ (φ₀ (β' P)) = (m : ℤ) • P := fun P => by
    rw [← comp_conj_apply hchar P]
    exact (DFunLike.congr_fun hβfac (β' P)).symm
  have hkill₀ : ∀ T : W.toAffine.Point, (m : ℤ) • T = 0 → φ₀ (β' T) = 0 := by
    intro T hT
    have h1 : β' T ∈ β.ker := by
      rw [AddMonoidHom.mem_ker]
      exact (comp_conj_apply hchar T).trans (by rw [hT])
    rw [← hkerφ₀] at h1
    exact h1
  obtain ⟨τ, hτ, hι₀τ, hτι₀⟩ := exists_inverse W hφ₀rat hm hι₀ hι₀inj hβ'rat hββ' hkill₀

  obtain ⟨γ₀, hγ₀, hpt⟩ :=
    WeierstrassCurve.exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id
      (W.veluQuotient (W.oddOrderSummingSet Q₀ n)) W ι₀ hι₀ τ hτ hτι₀ hι₀τ
  refine ⟨γ₀, hγ₀, fun P => ?_⟩
  rw [← hpt (φ₀ P)]
  exact DFunLike.congr_fun hβfac P

end Main

end WeierstrassCurve.KernelIsoVC

theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W)
    (s : ℤ) (n : ℕ)
    (hchar : β.comp β + ((2 * n + 1 : ℕ) : ℤ) • AddMonoidHom.id _ = s • β)
    (hirr : ∀ x : ℤ, x ^ 2 - s * x + (2 * n + 1 : ℕ) ≠ 0)
    (hprim : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ s → ¬ (ℓ : ℤ) ^ 2 ∣ ((2 * n + 1 : ℕ) : ℤ))
    (hm : ((2 * n + 1 : ℕ) : k) ≠ 0)
    (Q₀ : W.toAffine.Point) (hQ₀ : addOrderOf Q₀ = 2 * n + 1) (hQ₀β : β Q₀ = 0)
    (φ₀ : W.toAffine.Point →+ (W.veluQuotient (W.oddOrderSummingSet Q₀ n)).toAffine.Point)
    (hφ₀ker : φ₀.ker = AddSubgroup.zmultiples Q₀)
    (hφ₀ : ∀ (x y : k) (h : W.toAffine.Nonsingular x y),
      (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q₀ →
        ∃ h', φ₀ (.some x y h) = .some (W.veluX (W.oddOrderSummingSet Q₀ n) x)
          (W.veluY (W.oddOrderSummingSet Q₀ n) x y) h') :
    ∃ (γ₀ : WeierstrassCurve.VariableChange k)
      (hγ₀ : γ₀ • W = W.veluQuotient (W.oddOrderSummingSet Q₀ n)),
      ∀ P, β P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ₀ (φ₀ P) :=
  WeierstrassCurve.KernelIsoVC.main W hβ s n hchar hirr hprim hm Q₀ hQ₀ hQ₀β φ₀ hφ₀ker hφ₀

end S_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient_forall_apply_eq_of_comp_self_add_smul_eq_smul (solution)
