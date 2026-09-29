-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/868f4008-0cad-5533-bb1b-a9ce5519b7d1

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_natDegree_lt_of_xCoord_rep
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero
import Theorems.Thm_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_natDegree_Phi_sub_C_mul_PsiSq
import Theorems.Thm_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine.map_slope Affine Affine.Point.add_of_Y_eq natDegree_Φ map map_j Affine.Point.some Affine.Point.some.injEq exists_variableChange_of_j_eq Affine.degree_polynomial Affine.Point.some.inj ΨSq_ne_zero Affine.map_addY Φ_ne_zero Affine.map_addX ΨSq toAffine Affine.Point Affine.Point.add_some Affine.nonsingular_neg Affine.monic_polynomial Affine.Point.some_ne_zero VariableChange Affine.map_negY Affine.Y_eq_of_X_eq Affine.map_nonsingular leadingCoeff_Φ Affine.Point.neg_some baseChange j evalEvalBC IsRationallyRepresented rationalHomSet exists_xCoord_rep_of_mem_rationalHomSet surjective_of_mem_rationalHomSet natDegree_lt_of_xCoord_rep exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand comp_mem_rationalHomSet card_torsion_of_isAlgClosed exists_isDualPair_of_mem_rationalHomSet exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero Affine.Point.zsmul_some_eq_some_div Affine.Point.smul_some_eq_zero_iff Affine.evalEval_psi_sq isCoprime_Phi_PsiSq natDegree_Phi_sub_C_mul_PsiSq exists_addEquiv_point_variableChange"
namespace SeparableToSupersingular
p2m_open "WeierstrassCurve"

section MapPt

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

noncomputable def mapPt (W : WeierstrassCurve F) (f : F →+* K) :
    W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (f x) (f y) ((WeierstrassCurve.Affine.map_nonsingular W f.injective x y).mpr h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right,
        WeierstrassCurve.Affine.Point.add_of_Y_eq (congr_arg f hxy.left) (by
          rw [hxy.right]; exact (WeierstrassCurve.Affine.map_negY f x₂ y₂).symm)]
    · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
        rintro ⟨hx, hy⟩
        rw [WeierstrassCurve.Affine.map_negY] at hy
        exact hxy ⟨f.injective hx, f.injective hy⟩
      rw [WeierstrassCurve.Affine.Point.add_some hxy, WeierstrassCurve.Affine.Point.add_some hxy']
      simp only [WeierstrassCurve.Affine.map_addX, WeierstrassCurve.Affine.map_addY,
        WeierstrassCurve.Affine.map_slope]

theorem mapPt_zero (W : WeierstrassCurve F) (f : F →+* K) : mapPt W f 0 = 0 := rfl

theorem mapPt_some (W : WeierstrassCurve F) (f : F →+* K) {x y : F} (h : W.toAffine.Nonsingular x y) :
    mapPt W f (.some x y h) =
      .some (f x) (f y) ((WeierstrassCurve.Affine.map_nonsingular W f.injective x y).mpr h) := rfl

theorem mapPt_injective (W : WeierstrassCurve F) (f : F →+* K) : Function.Injective (mapPt W f) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · exact absurd h (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · rw [mapPt_some, mapPt_some] at h
    obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj h
    cases f.injective hx
    cases f.injective hy
    rfl

end MapPt

section Helper

variable {k : Type*} [Field k]

theorem exists_eq_some' {W : WeierstrassCurve k} {P : W.toAffine.Point} {u v u' v' : k}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀) (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

end Helper

section Frobenius

variable {κ : Type*} [Field κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]

theorem mapPt_iterateFrobenius_mem_rationalHomSet (W : WeierstrassCurve κ) (n : ℕ) :
    (mapPt W (iterateFrobenius κ p n) :
      (W.baseChange κ).toAffine.Point →+ ((W.map (iterateFrobenius κ p n)).baseChange κ).toAffine.Point) ∈
      WeierstrassCurve.rationalHomSet κ W (W.map (iterateFrobenius κ p n)) := by
  right
  refine ⟨C (X ^ p ^ n), 1, X ^ p ^ n, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : WeierstrassCurve.evalEvalBC (F := κ) κ (1 : κ[X][Y]) x y = 1 := by
    simp [WeierstrassCurve.evalEvalBC, Polynomial.evalEval]
  have e1 : WeierstrassCurve.evalEvalBC (F := κ) κ (C (X ^ p ^ n) : κ[X][Y]) x y = x ^ p ^ n := by
    simp [WeierstrassCurve.evalEvalBC, Polynomial.evalEval]
  have e2 : WeierstrassCurve.evalEvalBC (F := κ) κ (X ^ p ^ n : κ[X][Y]) x y = y ^ p ^ n := by
    simp [WeierstrassCurve.evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  have hP : mapPt W (iterateFrobenius κ p n) (.some x y h) = .some (x ^ p ^ n) (y ^ p ^ n)
      ((WeierstrassCurve.Affine.map_nonsingular W (iterateFrobenius κ p n).injective x y).mpr h) := by
    rw [mapPt_some]; rfl
  exact exists_eq_some' hP (by rw [e0, e1, div_one]) (by rw [e0, e2, div_one])

theorem mapPt_iterateFrobenius_some (W : WeierstrassCurve κ) (n : ℕ) {x y : κ} (h : W.toAffine.Nonsingular x y) :
    ∃ h', mapPt W (iterateFrobenius κ p n) (.some x y h) = .some (x ^ p ^ n) (y ^ p ^ n) h' :=
  ⟨_, by rw [mapPt_some]; rfl⟩

end Frobenius

section XRepCalc

variable {κ : Type*} [Field κ]

def XRep (p : ℕ) {W₁ W₂ : WeierstrassCurve κ} (α : W₁.toAffine.Point → W₂.toAffine.Point)
    (u v : κ[X]) (e : ℕ) (B : Set κ) : Prop :=
  ∀ (x y : κ) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
    ∃ (x' y' : κ) (h' : W₂.toAffine.Nonsingular x' y'),
      α (.some x y h) = .some x' y' h' ∧ x' * v.eval (x ^ p ^ e) = u.eval (x ^ p ^ e)

variable {p : ℕ} {W₁ W₂ : WeierstrassCurve κ}

theorem XRep.mono {α : W₁.toAffine.Point → W₂.toAffine.Point} {u v : κ[X]} {e : ℕ} {B B' : Set κ}
    (h : XRep p α u v e B) (hBB' : B ⊆ B') : XRep p α u v e B' :=
  fun x y hxy hx => h x y hxy fun hb => hx (hBB' hb)

theorem XRep.of_expand {α : W₁.toAffine.Point → W₂.toAffine.Point} {u v : κ[X]} {e m : ℕ} {B : Set κ}
    (h : XRep p α (expand κ (p ^ m) u) (expand κ (p ^ m) v) e B) : XRep p α u v (e + m) B := by
  intro x y hxy hx
  obtain ⟨x', y', h', hP, hx'⟩ := h x y hxy hx
  refine ⟨x', y', h', hP, ?_⟩
  rwa [expand_eval, expand_eval, ← pow_mul, ← pow_add] at hx'

theorem XRep.expand {α : W₁.toAffine.Point → W₂.toAffine.Point} {u v : κ[X]} {e m : ℕ} {B : Set κ}
    (h : XRep p α u v (e + m) B) : XRep p α (Polynomial.expand κ (p ^ m) u) (Polynomial.expand κ (p ^ m) v) e B := by
  intro x y hxy hx
  obtain ⟨x', y', h', hP, hx'⟩ := h x y hxy hx
  refine ⟨x', y', h', hP, ?_⟩
  rwa [expand_eval, expand_eval, ← pow_mul, ← pow_add]

theorem exists_nonsingular [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] (x : κ) :
    ∃ y : κ, W.toAffine.Nonsingular x y := by
  have hdeg : (W.toAffine.polynomial.map (Polynomial.evalRingHom x)).degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.monic_polynomial.degree_map, WeierstrassCurve.Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, (W.toAffine.equation_iff_nonsingular).mp ?_⟩
  rw [Polynomial.IsRoot.def, Polynomial.map_evalRingHom_eval] at hy
  exact hy

theorem XRep.mul_eq_mul [IsAlgClosed κ] [W₁.IsElliptic] [Fact p.Prime] [CharP κ p]
    {α : W₁.toAffine.Point → W₂.toAffine.Point}
    {u v u' v' : κ[X]} {e : ℕ} {B B' : Set κ} (hB : B.Finite) (hB' : B'.Finite)
    (h : XRep p α u v e B) (h' : XRep p α u' v' e B') : u * v' = v * u' := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : ((iterateFrobenius κ p e) '' (B ∪ B')ᶜ).Infinite :=
    ((hB.union hB').infinite_compl).image (iterateFrobenius κ p e).injective.injOn
  refine hinf.mono ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hx
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x₁, y₁, h₁, hP₁, hx₁⟩ := h x y hy hx.1
  obtain ⟨x₂, y₂, h₂, hP₂, hx₂⟩ := h' x y hy hx.2
  rw [hP₁] at hP₂
  obtain ⟨rfl, -⟩ := WeierstrassCurve.Affine.Point.some.inj hP₂
  simp only [Set.mem_setOf_eq, eval_mul, iterateFrobenius_def]
  rw [← hx₁, ← hx₂]
  ring

theorem XRep.false_of_wronskian_ne_zero [IsAlgClosed κ] [W₁.IsElliptic] [Fact p.Prime] [CharP κ p]
    {α : W₁.toAffine.Point → W₂.toAffine.Point}
    {u v : κ[X]} {B : Set κ} (hw : wronskian u v ≠ 0) (hB : B.Finite) (h : XRep p α u v 0 B)
    {A D : κ[X]} {g : ℕ} (hg : 1 ≤ g) (hD : D ≠ 0) {B' : Set κ} (hB' : B'.Finite)
    (h' : XRep p α A D g B') : False := by
  have h'' : XRep p α (Polynomial.expand κ (p ^ g) A) (Polynomial.expand κ (p ^ g) D) 0 B' :=
    XRep.expand (by rwa [zero_add])
  have e1 := XRep.mul_eq_mul hB hB' h h''

  have hp : (p : κ[X]) ^ g = 0 := by
    obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le hg
    rw [pow_add, pow_one]
    have : (p : κ[X]) = 0 := by
      rw [← C_eq_natCast, CharP.cast_eq_zero κ p, map_zero]
    rw [this, zero_mul]
  have hdS : derivative (Polynomial.expand κ (p ^ g) D) = 0 := by
    rw [derivative_expand, Nat.cast_pow, hp, zero_mul, mul_zero]
  have hdR : derivative (Polynomial.expand κ (p ^ g) A) = 0 := by
    rw [derivative_expand, Nat.cast_pow, hp, zero_mul, mul_zero]
  have e2 := congrArg derivative e1
  rw [derivative_mul, derivative_mul, hdS, hdR, mul_zero, add_zero, mul_zero, add_zero] at e2

  have hS : Polynomial.expand κ (p ^ g) D ≠ 0 := by
    rwa [Ne, expand_eq_zero (pow_pos (Fact.out : p.Prime).pos g)]
  have key : (Polynomial.expand κ (p ^ g) D) ^ 2 * wronskian u v = 0 := by
    rw [wronskian]
    linear_combination (Polynomial.expand κ (p ^ g) D * derivative v) * e1 -
      (Polynomial.expand κ (p ^ g) D * v) * e2
  rcases mul_eq_zero.mp key with h0 | h0
  · exact hS (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
  · exact hw h0

theorem isCoprime_of_expand [IsAlgClosed κ] {q : ℕ} (hq : 0 < q) {u v : κ[X]}
    (h : IsCoprime (Polynomial.expand κ q u) (Polynomial.expand κ q v)) : IsCoprime u v := by
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := κ) κ u v).mpr fun a => ?_
  obtain ⟨b, rfl⟩ := IsAlgClosed.exists_pow_nat_eq a hq
  have := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := κ) κ _ _).mp h b
  simpa only [coe_aeval_eq_eval, expand_eval] using this

theorem exists_XRep_wronskian [DecidableEq κ] [IsAlgClosed κ] [W₁.IsElliptic] [W₂.IsElliptic] [Fact p.Prime] [CharP κ p]
    (α : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (hα : α ∈ WeierstrassCurve.rationalHomSet κ W₁ W₂) (hα0 : α ≠ 0) :
    ∃ (u v : κ[X]) (e : ℕ) (B : Set κ), IsCoprime u v ∧ wronskian u v ≠ 0 ∧ B.Finite ∧ XRep p α u v e B := by
  obtain ⟨u₀, v₀, B, hc₀, hB, hrep₀⟩ := WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet κ W₁ W₂ hα hα0
  have hrep₀' : XRep p α u₀ v₀ 0 B := by
    intro x y h hx
    obtain ⟨x', y', h', hP, hx'⟩ := hrep₀ x y h hx
    exact ⟨x', y', h', hP, by simpa only [pow_zero, pow_one] using hx'⟩

  have hdeg : ∀ (u v : κ[X]) (e : ℕ), IsCoprime u v → XRep p α u v e B → 1 ≤ u.natDegree := by
    intro u v e hc hrep
    have hrep' : XRep p α (Polynomial.expand κ (p ^ e) u) (Polynomial.expand κ (p ^ e) v) 0 B :=
      XRep.expand (by rwa [zero_add])
    have hcx : IsCoprime (Polynomial.expand κ (p ^ e) u) (Polynomial.expand κ (p ^ e) v) :=
      hc.map (Polynomial.expand κ (p ^ e)).toRingHom
    have hlt := WeierstrassCurve.natDegree_lt_of_xCoord_rep W₁ W₂ α (u := Polynomial.expand κ (p ^ e) u)
      (v := Polynomial.expand κ (p ^ e) v) (B := B) hcx hB (by
        intro x y h hx
        obtain ⟨x', y', h', hP, hx'⟩ := hrep' x y h hx
        exact ⟨x', y', h', hP, by simpa only [pow_zero, pow_one] using hx'⟩)
    rw [natDegree_expand, natDegree_expand] at hlt
    rcases Nat.eq_zero_or_pos u.natDegree with h0 | h0
    · rw [h0, zero_mul] at hlt; exact absurd hlt (Nat.not_lt_zero _)
    · exact h0
  suffices H : ∀ (n : ℕ) (u v : κ[X]) (e : ℕ), u.natDegree ≤ n → IsCoprime u v → XRep p α u v e B →
      ∃ (u v : κ[X]) (e : ℕ) (B : Set κ), IsCoprime u v ∧ wronskian u v ≠ 0 ∧ B.Finite ∧ XRep p α u v e B from
    H _ u₀ v₀ 0 le_rfl hc₀ hrep₀'
  intro n
  induction n with
  | zero =>
    intro u v e hn hc hrep
    exact absurd (le_trans (hdeg u v e hc hrep) hn) (by decide)
  | succ n ih =>
    intro u v e hn hc hrep
    by_cases hw : wronskian u v = 0
    · obtain ⟨hdu, hdv⟩ := hc.wronskian_eq_zero_iff.mp hw
      have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
      set u₁ := contract p u
      set v₁ := contract p v
      have hu : Polynomial.expand κ p u₁ = u := expand_contract p hdu hp0
      have hv : Polynomial.expand κ p v₁ = v := expand_contract p hdv hp0
      have hc₁ : IsCoprime u₁ v₁ := isCoprime_of_expand (Fact.out : p.Prime).pos (by rwa [hu, hv])
      have hrep₁ : XRep p α u₁ v₁ (e + 1) B := XRep.of_expand (m := 1) (by rwa [pow_one, hu, hv])
      refine ih u₁ v₁ (e + 1) ?_ hc₁ hrep₁
      have h1 := hdeg u v e hc hrep
      have hdeg₁ : u.natDegree = u₁.natDegree * p := by rw [← hu, natDegree_expand]
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      have : u₁.natDegree < u.natDegree := by
        rw [hdeg₁]
        have hu₁ : 1 ≤ u₁.natDegree := by
          rcases Nat.eq_zero_or_pos u₁.natDegree with h0 | h0
          · rw [hdeg₁, h0, zero_mul] at h1; exact absurd h1 (by decide)
          · exact h0
        nlinarith
      omega
    · exact ⟨u, v, e, B, hc, hw, hB, hrep⟩

end XRepCalc

section Torsion

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero.WeierstrassCurve"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [DecidableEq k]

def Good (W : WeierstrassCurve F) (B : Set k) (P : (W.baseChange k).toAffine.Point) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

omit [DecidableEq k] in
theorem finite_setOf_equation (W : WeierstrassCurve F) (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

omit [DecidableEq k] in
theorem finite_not_good (W : WeierstrassCurve F) {B : Set k} (hB : B.Finite) :
    {P : (W.baseChange k).toAffine.Point | ¬ Good W B P}.Finite := by
  have hfin : (insert (0 : (W.baseChange k).toAffine.Point)
      (⋃ x ∈ B, ⋃ y ∈ {y : k | (W.baseChange k).toAffine.Equation x y},
        {P : (W.baseChange k).toAffine.Point |
          ∃ h : (W.baseChange k).toAffine.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation (k := k) W x) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq, Good, not_exists, not_and, not_not] at hP
  rcases P with _ | ⟨x, y, h⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨x, hP x y h rfl, y, h.left, h, rfl⟩

theorem finite_ker {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : IsRationallyRepresented k W₁ W₂ α) : {P | α P = 0}.Finite := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine (finite_not_good W₁ hB).subset ?_
  rintro P (hP : α P = 0) ⟨x, y, h, rfl, hx⟩
  obtain ⟨-, -, h', hP'⟩ := hrep x y h hx
  rw [hP'] at hP
  exact absurd hP (by rintro ⟨⟩)

theorem isOfFinAddOrder_of_apply_eq_zero {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) {P : (W₁.baseChange k).toAffine.Point} (hP : α P = 0) :
    IsOfFinAddOrder P := by
  haveI : Finite α.ker := by
    have := (finite_ker (hα.resolve_left hα0)).to_subtype
    exact Finite.of_equiv {P | α P = 0} (Equiv.refl _)
  have h := isOfFinAddOrder_of_finite (⟨P, hP⟩ : α.ker)
  exact α.ker.subtype.isOfFinAddOrder h

theorem noTorsion_of_hom [IsAlgClosed k] {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {χ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hχ : χ ∈ rationalHomSet k W₁ W₂) (hχ0 : χ ≠ 0) (p : ℕ)
    (h₁ : ∀ P : (W₁.baseChange k).toAffine.Point, p • P = 0 → P = 0) :
    ∀ P : (W₂.baseChange k).toAffine.Point, p • P = 0 → P = 0 := by
  intro P hP
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hχ hχ0
  obtain ⟨Q, rfl⟩ := hsurj P
  set K : Set (W₁.baseChange k).toAffine.Point := {R | χ R = 0} with hK
  have hKfin : K.Finite := finite_ker (hχ.resolve_left hχ0)
  set S : Set (W₁.baseChange k).toAffine.Point := {R | χ (p • R) = 0} with hS
  have hinj : Set.InjOn (fun R : (W₁.baseChange k).toAffine.Point => p • R) Set.univ := by
    intro R _ R' _ hRR'
    have h0 : p • (R - R') = 0 := by
      simp only [smul_sub, sub_eq_zero]; exact hRR'
    exact sub_eq_zero.mp (h₁ _ h0)
  have hKS : K ⊆ S := by
    intro R hR
    simp only [hS, Set.mem_setOf_eq, map_nsmul]
    rw [show χ R = 0 from hR, smul_zero]
  have hmaps : ∀ R ∈ S, (fun R : (W₁.baseChange k).toAffine.Point => p • R) R ∈ K := fun R hR => hR
  have hle : S.ncard ≤ K.ncard :=
    Set.ncard_le_ncard_of_injOn (fun R => p • R) hmaps (hinj.mono (Set.subset_univ _)) hKfin
  have hSfin : S.Finite := by
    have : S = (fun R : (W₁.baseChange k).toAffine.Point => p • R) ⁻¹' K := rfl
    rw [this]
    exact hKfin.preimage (hinj.mono (Set.subset_univ _))
  have hKeq : K = S := Set.eq_of_subset_of_ncard_le hKS hle hSfin
  have hQS : Q ∈ S := by
    simp only [hS, Set.mem_setOf_eq, map_nsmul]
    exact hP
  rw [← hKeq] at hQS
  exact hQS

end Torsion

section ExpUnique

variable {κ : Type*} [Field κ] {p : ℕ} {W₁ W₂ : WeierstrassCurve κ}

theorem XRep.false_of_wronskian_ne_zero' [IsAlgClosed κ] [W₁.IsElliptic] [Fact p.Prime] [CharP κ p]
    {α : W₁.toAffine.Point → W₂.toAffine.Point}
    {u v : κ[X]} {e : ℕ} {B : Set κ} (hw : wronskian u v ≠ 0) (hB : B.Finite) (h : XRep p α u v e B)
    {A D : κ[X]} {g : ℕ} (hg : 1 ≤ g) (hD : D ≠ 0) {B' : Set κ} (hB' : B'.Finite)
    (h' : XRep p α A D (e + g) B') : False := by
  have h'' : XRep p α (Polynomial.expand κ (p ^ g) A) (Polynomial.expand κ (p ^ g) D) e B' := XRep.expand h'
  have e1 := XRep.mul_eq_mul hB hB' h h''
  have hp : (p : κ[X]) ^ g = 0 := by
    obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le hg
    rw [pow_add, pow_one]
    have : (p : κ[X]) = 0 := by
      rw [← C_eq_natCast, CharP.cast_eq_zero κ p, map_zero]
    rw [this, zero_mul]
  have hdS : derivative (Polynomial.expand κ (p ^ g) D) = 0 := by
    rw [derivative_expand, Nat.cast_pow, hp, zero_mul, mul_zero]
  have hdR : derivative (Polynomial.expand κ (p ^ g) A) = 0 := by
    rw [derivative_expand, Nat.cast_pow, hp, zero_mul, mul_zero]
  have e2 := congrArg derivative e1
  rw [derivative_mul, derivative_mul, hdS, hdR, mul_zero, add_zero, mul_zero, add_zero] at e2
  have hS : Polynomial.expand κ (p ^ g) D ≠ 0 := by
    rwa [Ne, expand_eq_zero (pow_pos (Fact.out : p.Prime).pos g)]
  have key : (Polynomial.expand κ (p ^ g) D) ^ 2 * wronskian u v = 0 := by
    rw [wronskian]
    linear_combination (Polynomial.expand κ (p ^ g) D * derivative v) * e1 -
      (Polynomial.expand κ (p ^ g) D * v) * e2
  rcases mul_eq_zero.mp key with h0 | h0
  · exact hS (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
  · exact hw h0

theorem XRep.exp_unique [IsAlgClosed κ] [W₁.IsElliptic] [Fact p.Prime] [CharP κ p]
    {α : W₁.toAffine.Point → W₂.toAffine.Point}
    {u v : κ[X]} {e : ℕ} {B : Set κ} (hw : wronskian u v ≠ 0) (hB : B.Finite) (h : XRep p α u v e B)
    {u' v' : κ[X]} {e' : ℕ} {B' : Set κ} (hw' : wronskian u' v' ≠ 0) (hB' : B'.Finite) (h' : XRep p α u' v' e' B') :
    e = e' := by
  have hv : v ≠ 0 := by rintro rfl; exact hw (wronskian_zero_right u)
  have hv' : v' ≠ 0 := by rintro rfl; exact hw' (wronskian_zero_right u')
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    exact (XRep.false_of_wronskian_ne_zero' hw hB h (g := g + 1) (by omega) hv' hB' (by rwa [← add_assoc])).elim
  · exact heq
  · obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    exact (XRep.false_of_wronskian_ne_zero' hw' hB' h' (g := g + 1) (by omega) hv hB (by rwa [← add_assoc])).elim

end ExpUnique

section Comp

variable {κ : Type*} [Field κ] {p : ℕ} [Fact p.Prime] [CharP κ p]

theorem eval_pow_iterateFrobenius (u : κ[X]) (k : ℕ) (t : κ) :
    (u.eval t) ^ p ^ k = (u.map (iterateFrobenius κ p k)).eval (t ^ p ^ k) := by
  rw [← iterateFrobenius_def, ← iterateFrobenius_def (R := κ) p k t, eval_map, eval₂_hom]

theorem wronskian_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u v : R[X]) :
    wronskian (u.map f) (v.map f) = (wronskian u v).map f := by
  simp only [wronskian, derivative_map, Polynomial.map_mul, Polynomial.map_sub]

noncomputable def hom (m : ℕ) (u v q : κ[X]) : κ[X] :=
  ∑ i ∈ Finset.range (m + 1), C (q.coeff i) * u ^ i * v ^ (m - i)

omit [Fact p.Prime] [CharP κ p] in
theorem eval_hom {m : ℕ} {u v q : κ[X]} (hq : q.natDegree ≤ m) {x : κ} (hx : v.eval x ≠ 0) :
    (hom m u v q).eval x = (v.eval x) ^ m * q.eval (u.eval x / v.eval x) := by
  simp only [hom, eval_finsetSum, eval_mul, eval_pow, eval_C]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [div_pow, show (v.eval x) ^ m = (v.eval x) ^ i * (v.eval x) ^ (m - i) by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hi)]]
  field_simp

variable {W₁ W₂ W₃ : WeierstrassCurve κ}

theorem XRep.comp [IsAlgClosed κ] [W₁.IsElliptic]
    {α : W₁.toAffine.Point → W₂.toAffine.Point} {β : W₂.toAffine.Point → W₃.toAffine.Point}
    {u v : κ[X]} {a : ℕ} {B : Set κ} (hc : IsCoprime u v) (hu : 0 < max u.natDegree v.natDegree)
    (hw : wronskian u v ≠ 0) (hB : B.Finite) (hα : XRep p α u v a B)
    {r s : κ[X]} {b : ℕ} {B' : Set κ} (hc' : IsCoprime r s) (hr : 0 < max r.natDegree s.natDegree)
    (hw' : wronskian r s ≠ 0) (hB' : B'.Finite) (hβ : XRep p β r s b B') :
    ∃ (U V : κ[X]) (B'' : Set κ), IsCoprime U V ∧ 0 < max U.natDegree V.natDegree ∧ wronskian U V ≠ 0 ∧ B''.Finite ∧
      XRep p (β ∘ α) U V (a + b) B'' := by
  set σ := iterateFrobenius κ p b with hσ
  set uσ := u.map σ with huσ
  set vσ := v.map σ with hvσ
  set N := max r.natDegree s.natDegree with hN
  have hcσ : IsCoprime uσ vσ := hc.map (mapRingHom σ)
  have huσdeg : 0 < max uσ.natDegree vσ.natDegree := by
    rwa [huσ, hvσ, natDegree_map_eq_of_injective σ.injective, natDegree_map_eq_of_injective σ.injective]
  have hwσ : wronskian uσ vσ ≠ 0 := by
    rw [huσ, hvσ, wronskian_map]
    exact (Polynomial.map_ne_zero_iff σ.injective).mpr hw
  obtain ⟨hcUV, hUVdeg, hwUV⟩ := Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero (U := hom N uσ vσ r)
    (V := hom N uσ vσ s) hcσ huσdeg hwσ hc' hr hw'
    (fun x hx => eval_hom (le_max_left _ _) hx) (fun x hx => eval_hom (le_max_right _ _) hx)

  have hne : ∀ c : κ, u - C c * v ≠ 0 := by
    intro c h0
    rw [sub_eq_zero] at h0
    have hvunit : IsUnit v := hc.isUnit_of_dvd' (by rw [h0]; exact dvd_mul_left v (C c)) dvd_rfl
    have hv0 : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hvunit
    have hu0 : u.natDegree = 0 := by
      rw [h0]
      refine le_antisymm ((natDegree_mul_le).trans ?_) (Nat.zero_le _)
      rw [natDegree_C, hv0]
    rw [hu0, hv0, max_self] at hu
    exact lt_irrefl 0 hu

  have hvT : ∀ (T x₁ : κ), x₁ * v.eval T = u.eval T → v.eval T ≠ 0 := by
    intro T x₁ hx₁ hv0
    rw [hv0, mul_zero] at hx₁
    rcases (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := κ) κ u v).mp hc T with h1 | h1
    · exact h1 (by rw [coe_aeval_eq_eval]; exact hx₁.symm)
    · exact h1 (by rw [coe_aeval_eq_eval]; exact hv0)

  set σa := iterateFrobenius κ p a with hσa
  set B'' : Set κ := B ∪ σa ⁻¹' (⋃ c ∈ B', {t | (u - C c * v).IsRoot t}) with hB''
  have hB''fin : B''.Finite := by
    refine hB.union (Set.Finite.preimage σa.injective.injOn ?_)
    exact Set.Finite.biUnion hB' fun c _ => Polynomial.finite_setOf_isRoot (hne c)
  refine ⟨hom N uσ vσ r, hom N uσ vσ s, B'', hcUV, hUVdeg, hwUV, hB''fin, ?_⟩
  intro x y h hx
  rw [hB'', Set.mem_union, not_or, Set.mem_preimage, Set.mem_iUnion₂, not_exists] at hx
  obtain ⟨hxB, hxB'⟩ := hx
  obtain ⟨x₁, y₁, h₁, hP₁, hx₁⟩ := hα x y h hxB
  have hv1 : v.eval (x ^ p ^ a) ≠ 0 := hvT _ _ hx₁
  have hx₁' : x₁ = u.eval (x ^ p ^ a) / v.eval (x ^ p ^ a) := by rw [eq_div_iff hv1]; exact hx₁
  have hx₁B : x₁ ∉ B' := by
    intro hmem
    refine hxB' x₁ ⟨hmem, ?_⟩
    show (u - C x₁ * v).IsRoot (σa x)
    rw [IsRoot.def, hσa, iterateFrobenius_def, eval_sub, eval_mul, eval_C, ← hx₁, sub_self]
  obtain ⟨x₂, y₂, h₂, hP₂, hx₂⟩ := hβ x₁ y₁ h₁ hx₁B
  refine ⟨x₂, y₂, h₂, by rw [Function.comp_apply, hP₁, hP₂], ?_⟩

  have hT' : x ^ p ^ (a + b) = (x ^ p ^ a) ^ p ^ b := by rw [pow_add, pow_mul]
  have hvσT : vσ.eval (x ^ p ^ (a + b)) = (v.eval (x ^ p ^ a)) ^ p ^ b := by
    rw [hT', hvσ, ← eval_pow_iterateFrobenius]
  have huσT : uσ.eval (x ^ p ^ (a + b)) = (u.eval (x ^ p ^ a)) ^ p ^ b := by
    rw [hT', huσ, ← eval_pow_iterateFrobenius]
  have hvσ0 : vσ.eval (x ^ p ^ (a + b)) ≠ 0 := by rw [hvσT]; exact pow_ne_zero _ hv1
  have hquot : uσ.eval (x ^ p ^ (a + b)) / vσ.eval (x ^ p ^ (a + b)) = x₁ ^ p ^ b := by
    rw [huσT, hvσT, ← div_pow, ← hx₁']
  rw [eval_hom (le_max_left _ _) hvσ0, eval_hom (le_max_right _ _) hvσ0, hquot, ← hx₂]
  ring

end Comp

section MulN

variable {κ : Type*} [Field κ] [DecidableEq κ]

theorem xrep_nsmul (p : ℕ) (E : WeierstrassCurve κ) [E.IsElliptic] {n : ℕ} (hn : (n : κ) ≠ 0) :
    ∃ B : Set κ, B.Finite ∧ XRep p (fun P : E.toAffine.Point => n • P) (E.Φ n) (E.ΨSq n) 0 B := by
  have hn' : ((n : ℤ) : κ) ≠ 0 := by rwa [Int.cast_natCast]
  have hΨ0 : E.ΨSq n ≠ 0 := WeierstrassCurve.ΨSq_ne_zero (W := E) hn'
  refine ⟨{x | (E.ΨSq n).IsRoot x}, Polynomial.finite_setOf_isRoot hΨ0, ?_⟩
  intro x y h hx
  have hψ : (E.ψ n).evalEval x y ≠ 0 := by
    intro h0
    have := WeierstrassCurve.Affine.evalEval_psi_sq E h.left (n : ℤ)
    rw [h0, zero_pow two_ne_zero] at this
    exact hx this.symm
  obtain ⟨y', h', hP⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div E h (n := n) hψ
  refine ⟨_, y', h', by show n • _ = _; rw [← natCast_zsmul]; exact hP, ?_⟩
  simp only [pow_zero, pow_one]
  rw [div_mul_cancel₀ _ hx]

omit [DecidableEq κ] in

theorem wronskian_Phi_PsiSq_ne_zero (p : ℕ) [Fact p.Prime] [CharP κ p] (E : WeierstrassCurve κ) [E.IsElliptic] {n : ℕ}
    (hn : (n : κ) ≠ 0) : wronskian (E.Φ n) (E.ΨSq n) ≠ 0 := by
  intro hw
  obtain ⟨hdΦ, -⟩ := (WeierstrassCurve.isCoprime_Phi_PsiSq E n).wronskian_eq_zero_iff.mp hw
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hexp := expand_contract p hdΦ hp0
  have hdeg := congrArg natDegree hexp
  rw [natDegree_expand, WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast] at hdeg
  have hdvd : p ∣ n ^ 2 := ⟨_, by rw [← hdeg, mul_comm]⟩
  have hpn : p ∣ n := (Fact.out : p.Prime).dvd_of_dvd_pow hdvd
  apply hn
  obtain ⟨m, rfl⟩ := hpn
  rw [Nat.cast_mul, CharP.cast_eq_zero κ p, zero_mul]

omit [DecidableEq κ] in
theorem natDegree_Phi_pos (E : WeierstrassCurve κ) {n : ℕ} (hn : n ≠ 0) :
    0 < max (E.Φ n).natDegree (E.ΨSq n).natDegree := by
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  rw [WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast]
  positivity

end MulN

section MulP

variable {κ : Type*} [Field κ] [DecidableEq κ] [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]

omit [CharP κ p] in

theorem Phi_PsiSq_of_supersingular (X : WeierstrassCurve κ) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    ∃ b d : κ, d ≠ 0 ∧ X.ΨSq p = C d ∧ X.Φ p = Polynomial.X ^ p ^ 2 + C b := by

  have hψ : ∀ (x y : κ) (h : X.toAffine.Nonsingular x y), (X.ψ p).evalEval x y ≠ 0 := by
    intro x y h h0
    have h1 : ((p : ℤ)) • (WeierstrassCurve.Affine.Point.some x y h) = 0 :=
      (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff X h (p : ℤ)).mpr h0
    rw [natCast_zsmul] at h1
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ (hss _ h1)

  have hΨroot : ∀ x : κ, (X.ΨSq p).eval x ≠ 0 := by
    intro x
    obtain ⟨y, h⟩ := exists_nonsingular X x
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq X h.left (p : ℤ)]
    exact pow_ne_zero 2 (hψ x y h)
  have hΨdeg : (X.ΨSq p).degree = 0 := by
    by_contra hd
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X.ΨSq p) hd
    exact hΨroot x hx
  set d := (X.ΨSq p).coeff 0 with hddef
  have hΨC : X.ΨSq p = C d := eq_C_of_degree_eq_zero hΨdeg
  have hd0 : d ≠ 0 := by
    intro h0
    apply hΨroot 0
    rw [hΨC, h0, map_zero, eval_zero]

  have hmul : ∀ (x y : κ) (h : X.toAffine.Nonsingular x y),
      ∃ y' h', p • (WeierstrassCurve.Affine.Point.some x y h : X.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some ((X.Φ p).eval x / d) y' h' := by
    intro x y h
    obtain ⟨y', h', hP⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div X h (n := p) (hψ x y h)
    have hev : (X.ΨSq p).eval x = d := by rw [hΨC, eval_C]
    rw [natCast_zsmul] at hP
    exact ⟨y', exists_eq_some' hP (by rw [hev]) rfl⟩

  have hinj : ∀ x₁ x₂ : κ, (X.Φ p).eval x₁ = (X.Φ p).eval x₂ → x₁ = x₂ := by
    intro x₁ x₂ hΦ
    obtain ⟨y₁, h₁⟩ := exists_nonsingular X x₁
    obtain ⟨y₂, h₂⟩ := exists_nonsingular X x₂
    obtain ⟨y₁', h₁', hP₁⟩ := hmul x₁ y₁ h₁
    obtain ⟨y₂', h₂', hP₂⟩ := hmul x₂ y₂ h₂
    have hxx : (X.Φ p).eval x₁ / d = (X.Φ p).eval x₂ / d := by rw [hΦ]
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁'.left h₂'.left hxx with hy | hy
    ·
      have heq : p • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : X.toAffine.Point) =
          p • WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
        rw [hP₁, hP₂]
        exact WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _ |>.mpr ⟨hxx, hy⟩
      have h0 : p • ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : X.toAffine.Point) -
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0 := by rw [smul_sub, heq, sub_self]
      have := sub_eq_zero.mp (hss _ h0)
      exact (WeierstrassCurve.Affine.Point.some.inj this).left
    ·
      have heq : p • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : X.toAffine.Point) =
          -(p • WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) := by
        rw [hP₁, hP₂, WeierstrassCurve.Affine.Point.neg_some]
        exact WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _ |>.mpr ⟨hxx, hy⟩
      have h0 : p • ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : X.toAffine.Point) +
          WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0 := by rw [smul_add, heq, neg_add_cancel]
      have := eq_neg_of_add_eq_zero_left (hss _ h0)
      rw [WeierstrassCurve.Affine.Point.neg_some] at this
      exact (WeierstrassCurve.Affine.Point.some.inj this).left

  set b := (X.Φ p).eval 0 with hbdef
  set F := X.Φ p - C b with hF
  have hFdeg : F.natDegree = p ^ 2 := by
    have := WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq X p (b * d⁻¹)
    rwa [hΨC, ← C_mul, inv_mul_cancel_right₀ hd0, Int.natAbs_natCast] at this
  have hΦdeg : 0 < (X.Φ p).degree := by
    rw [degree_eq_natDegree (WeierstrassCurve.Φ_ne_zero (W := X) p), WeierstrassCurve.natDegree_Φ, Int.natAbs_natCast]
    exact_mod_cast pow_pos (Fact.out : p.Prime).pos 2
  have hFmonic : F.Monic := by
    rw [Monic, hF, leadingCoeff_sub_of_degree_lt (lt_of_le_of_lt degree_C_le hΦdeg), WeierstrassCurve.leadingCoeff_Φ]
  have hFroots : F.roots = Multiset.replicate (p ^ 2) 0 := by
    rw [Multiset.eq_replicate]
    refine ⟨by rw [IsAlgClosed.card_roots_eq_natDegree, hFdeg], fun x hx => ?_⟩
    have hx' : F.IsRoot x := (mem_roots hFmonic.ne_zero).mp hx
    rw [IsRoot.def, hF, eval_sub, eval_C, sub_eq_zero] at hx'
    exact hinj x 0 hx'
  have hFeq : F = Polynomial.X ^ p ^ 2 := by
    have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFmonic
      (by rw [IsAlgClosed.card_roots_eq_natDegree])
    rw [hFroots, Multiset.map_replicate, Multiset.prod_replicate, map_zero, sub_zero] at this
    exact this.symm
  refine ⟨b, d, hd0, hΨC, ?_⟩
  rw [← sub_eq_iff_eq_add, ← hF, hFeq]

omit [CharP κ p] in

theorem xrep_char_smul (X : WeierstrassCurve κ) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    ∃ b d : κ, d ≠ 0 ∧ XRep p (fun P : X.toAffine.Point => p • P) (Polynomial.X + C b) (C d) 2 ∅ := by
  obtain ⟨b, d, hd0, hΨ, hΦ⟩ := Phi_PsiSq_of_supersingular p X hss
  refine ⟨b, d, hd0, fun x y h _ => ?_⟩
  have hψ : (X.ψ p).evalEval x y ≠ 0 := by
    intro h0
    have := WeierstrassCurve.Affine.evalEval_psi_sq X h.left (p : ℤ)
    rw [h0, zero_pow two_ne_zero, hΨ, eval_C] at this
    exact hd0 this.symm
  obtain ⟨y', h', hP⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div X h (n := p) hψ
  refine ⟨_, y', h', by show p • _ = _; rw [← natCast_zsmul]; exact hP, ?_⟩
  simp only [hΨ, hΦ, eval_C, eval_add, eval_pow, eval_X]
  rw [div_mul_cancel₀ _ hd0]

end MulP

section Parity

variable {κ : Type*} [Field κ] [DecidableEq κ] [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]

omit [DecidableEq κ] [IsAlgClosed κ] [Fact p.Prime] [CharP κ p] in
theorem isCoprime_C_right (u : κ[X]) {d : κ} (hd : d ≠ 0) : IsCoprime u (C d) :=
  ⟨0, C d⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hd, C_1]⟩

omit [DecidableEq κ] [IsAlgClosed κ] [Fact p.Prime] [CharP κ p] in
theorem wronskian_linear_C {c d : κ} (b : κ) (hc : c ≠ 0) (hd : d ≠ 0) :
    wronskian (C c * (Polynomial.X + C b)) (C d) ≠ 0 := by
  rw [wronskian, derivative_C, mul_zero, zero_sub, derivative_mul, derivative_C, zero_mul, zero_add, derivative_add,
    derivative_X, derivative_C, add_zero, mul_one, neg_ne_zero, ← C_mul, Ne, C_eq_zero]
  exact mul_ne_zero hc hd

omit [DecidableEq κ] [IsAlgClosed κ] [Fact p.Prime] [CharP κ p] in
theorem natDegree_linear_pos {c : κ} (b : κ) (hc : c ≠ 0) (v : κ[X]) :
    0 < max (C c * (Polynomial.X + C b)).natDegree v.natDegree := by
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  rw [natDegree_C_mul hc, natDegree_X_add_C]
  exact one_pos

theorem xrep_pow_mul_nsmul (X : WeierstrassCurve κ) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) {n : ℕ} (hn : (n : κ) ≠ 0) (k : ℕ) :
    ∃ (U V : κ[X]) (B : Set κ), IsCoprime U V ∧ 0 < max U.natDegree V.natDegree ∧ wronskian U V ≠ 0 ∧ B.Finite ∧
      XRep p (fun P : X.toAffine.Point => (p ^ k * n) • P) U V (2 * k) B := by
  induction k with
  | zero =>
    obtain ⟨B, hB, hrep⟩ := xrep_nsmul p X hn
    have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
    refine ⟨X.Φ n, X.ΨSq n, B, WeierstrassCurve.isCoprime_Phi_PsiSq X n, natDegree_Phi_pos X hn0,
      wronskian_Phi_PsiSq_ne_zero p X hn, hB, ?_⟩
    simpa only [pow_zero, one_mul, mul_zero] using hrep
  | succ k ih =>
    obtain ⟨U, V, B, hcUV, hUV, hwUV, hB, hrep⟩ := ih
    obtain ⟨b, d, hd0, hrepp⟩ := xrep_char_smul p X hss
    have hrepp' : XRep p (fun P : X.toAffine.Point => p • P) (C 1 * (Polynomial.X + C b)) (C d) 2 ∅ := by
      rwa [C_1, one_mul]
    obtain ⟨U', V', B', hc', hUV', hw', hB', hrep'⟩ := XRep.comp (W₃ := X) hcUV hUV hwUV hB hrep
      (isCoprime_C_right _ hd0) (natDegree_linear_pos b one_ne_zero _) (wronskian_linear_C b one_ne_zero hd0)
      Set.finite_empty hrepp'
    refine ⟨U', V', B', hc', hUV', hw', hB', ?_⟩
    have hfun : (fun P : X.toAffine.Point => (p ^ (k + 1) * n) • P) =
        (fun P : X.toAffine.Point => p • P) ∘ (fun P : X.toAffine.Point => (p ^ k * n) • P) := by
      funext P
      rw [Function.comp_apply, pow_succ, mul_comm (p ^ k) p, mul_assoc, mul_smul]
    rw [hfun, show 2 * (k + 1) = 2 * k + 2 by ring]
    exact hrep'

omit [DecidableEq κ] [IsAlgClosed κ] [Fact p.Prime] [CharP κ p] in

theorem XRep.neg {W₁ W₂ : WeierstrassCurve κ} {α : W₁.toAffine.Point → W₂.toAffine.Point} {u v : κ[X]} {e : ℕ}
    {B : Set κ} (h : XRep p α u v e B) : XRep p (fun P => -α P) u v e B := by
  intro x y hxy hx
  obtain ⟨x', y', h', hP, hx'⟩ := h x y hxy hx
  exact ⟨x', _, (WeierstrassCurve.Affine.nonsingular_neg ..).mpr h',
    by show -α _ = _; rw [hP, WeierstrassCurve.Affine.Point.neg_some], hx'⟩

omit [Fact p.Prime] [CharP κ p] in

theorem XRep.natDegree_pos {W₁ W₂ : WeierstrassCurve κ} [W₁.IsElliptic] [W₂.IsElliptic]
    (α : W₁.toAffine.Point →+ W₂.toAffine.Point) {u v : κ[X]} {e : ℕ} {B : Set κ}
    (hc : IsCoprime u v) (hB : B.Finite) (hrep : XRep p α u v e B) : 0 < max u.natDegree v.natDegree := by
  have hrep' : XRep p α (Polynomial.expand κ (p ^ e) u) (Polynomial.expand κ (p ^ e) v) 0 B :=
    XRep.expand (by rwa [zero_add])
  have hcx : IsCoprime (Polynomial.expand κ (p ^ e) u) (Polynomial.expand κ (p ^ e) v) :=
    hc.map (Polynomial.expand κ (p ^ e)).toRingHom
  have hlt := WeierstrassCurve.natDegree_lt_of_xCoord_rep W₁ W₂ α (u := Polynomial.expand κ (p ^ e) u)
    (v := Polynomial.expand κ (p ^ e) v) (B := B) hcx hB (by
      intro x y h hx
      obtain ⟨x', y', h', hP, hx'⟩ := hrep' x y h hx
      exact ⟨x', y', h', hP, by simpa only [pow_zero, pow_one] using hx'⟩)
  rw [natDegree_expand, natDegree_expand] at hlt
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  rcases Nat.eq_zero_or_pos u.natDegree with h0 | h0
  · rw [h0, zero_mul] at hlt; exact absurd hlt (Nat.not_lt_zero _)
  · exact h0

theorem odd_of_comp_self_eq (X : WeierstrassCurve κ) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0)
    {α : X.toAffine.Point →+ X.toAffine.Point} {m : ℤ} (hm : m ≠ 0)
    (hαα : ∀ P : X.toAffine.Point, α (α P) = -(((p * m.natAbs ^ 2 : ℕ)) • P))
    {u v : κ[X]} {e : ℕ} {B : Set κ} (hc : IsCoprime u v) (hw : wronskian u v ≠ 0) (hB : B.Finite)
    (hrep : XRep p α u v e B) : Odd e := by
  have hu := XRep.natDegree_pos p α hc hB hrep

  obtain ⟨U₁, V₁, B₁, -, -, hw₁, hB₁, hrep₁⟩ := XRep.comp (W₃ := X) hc hu hw hB hrep hc hu hw hB hrep

  have hmn : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  obtain ⟨w, m₁, hm₁, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hmn p (Fact.out : p.Prime).ne_one
  have hm₁κ : ((m₁ ^ 2 : ℕ) : κ) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero 2 fun h => hm₁ ((CharP.cast_eq_zero_iff κ p m₁).mp h)
  obtain ⟨U₂, V₂, B₂, -, -, hw₂, hB₂, hrep₂⟩ := xrep_pow_mul_nsmul p X hss hm₁κ (2 * w + 1)
  have hM : p * m.natAbs ^ 2 = p ^ (2 * w + 1) * m₁ ^ 2 := by rw [hmeq]; ring
  have hrep₂' : XRep p (fun P : X.toAffine.Point => α (α P)) U₂ V₂ (2 * (2 * w + 1)) B₂ := by
    have hfun : (fun P : X.toAffine.Point => α (α P)) = fun P => -((p ^ (2 * w + 1) * m₁ ^ 2) • P) := by
      funext P; rw [hαα, hM]
    rw [hfun]
    exact XRep.neg p hrep₂
  have h2 := XRep.exp_unique hw₁ hB₁ hrep₁ hw₂ hB₂ hrep₂'
  exact ⟨w, by omega⟩

end Parity

section Aux

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero.WeierstrassCurve"

variable {κ : Type*} [Field κ] [DecidableEq κ]

scoped instance instIsEllipticBaseChangeSelf (W : WeierstrassCurve κ) [W.IsElliptic] : (W.baseChange κ).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap κ κ)).IsElliptic)

omit [DecidableEq κ] in
theorem infinite_point [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] :
    Infinite (W.baseChange κ).toAffine.Point := by
  choose f hf using exists_nonsingular (W.baseChange κ)
  refine Infinite.of_injective (fun x : κ => (Affine.Point.some x (f x) (hf x) : (W.baseChange κ).toAffine.Point)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

theorem exists_nsmul_ne_zero [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (hW : ∀ P : (W.baseChange κ).toAffine.Point, p • P = 0 → P = 0) {N : ℕ} (hN : N ≠ 0) :
    ∃ P : (W.baseChange κ).toAffine.Point, N • P ≠ 0 := by
  obtain ⟨k, m, hm, hNkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p (Fact.out : p.Prime).ne_one
  have hstrip : ∀ (j : ℕ) (P : (W.baseChange κ).toAffine.Point), (p ^ j) • P = 0 → P = 0 := by
    intro j
    induction j with
    | zero => intro P hP; simpa using hP
    | succ j ih =>
      intro P hP
      rw [pow_succ, mul_smul] at hP
      exact hW P (ih _ hP)
  by_contra hall
  push Not at hall
  have hm0 : m ≠ 0 := by rintro rfl; simp at hNkm; exact hN hNkm
  have hmκ : ((m : ℕ) : κ) ≠ 0 := fun h => hm ((CharP.cast_eq_zero_iff κ p m).mp h)
  have htors : ∀ P : (W.baseChange κ).toAffine.Point, P ∈ Submodule.torsionBy ℤ _ (m : ℤ) := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    have h1 : (p ^ k) • (m • P) = 0 := by
      rw [← mul_smul, ← hNkm]
      exact hall P
    have h2 := hstrip k _ h1
    rw [natCast_zsmul]
    exact h2
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W (n := m) hmκ
  haveI : Finite ↥(Submodule.torsionBy ℤ (W.baseChange κ).toAffine.Point (m : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact pow_ne_zero 2 hm0
  haveI := infinite_point W
  haveI : Finite (W.baseChange κ).toAffine.Point :=
    Finite.of_injective (fun P => (⟨P, htors P⟩ : ↥(Submodule.torsionBy ℤ _ (m : ℤ))))
      (fun P Q h => congrArg Subtype.val h)
  exact not_finite (W.baseChange κ).toAffine.Point

theorem exists_hom_of_variableChange (p : ℕ) (V V' : WeierstrassCurve κ) (γ : VariableChange κ) (hγ : γ • V = V') :
    ∃ e : V.toAffine.Point →+ V'.toAffine.Point,
      (e : (V.baseChange κ).toAffine.Point →+ (V'.baseChange κ).toAffine.Point) ∈ rationalHomSet κ V V' ∧
      XRep p e (C ((↑γ.u⁻¹ : κ) ^ 2) * (Polynomial.X + C (-γ.r))) (C 1) 0 ∅ := by
  subst hγ
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange V γ
  refine ⟨e.toAddMonoidHom, ?_, ?_⟩
  · right
    refine ⟨C (C ((↑γ.u⁻¹ : κ) ^ 2) * (X - C γ.r)), 1,
      C (C ((↑γ.u⁻¹ : κ) ^ 3)) * (Y - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))), 1, ∅,
      Set.finite_empty, fun x y h _ => ?_⟩
    have e0 : evalEvalBC (F := κ) κ (1 : κ[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
    have e1 : evalEvalBC (F := κ) κ (C (C ((↑γ.u⁻¹ : κ) ^ 2) * (X - C γ.r)) : κ[X][Y]) x y =
        (↑γ.u⁻¹ : κ) ^ 2 * (x - γ.r) := by
      simp [evalEvalBC, Polynomial.evalEval]
    have e2 : evalEvalBC (F := κ) κ
        (C (C ((↑γ.u⁻¹ : κ) ^ 3)) * (Y - C (C γ.s * X) + C (C (γ.s * γ.r - γ.t))) : κ[X][Y]) x y =
        (↑γ.u⁻¹ : κ) ^ 3 * (y - γ.s * x + (γ.s * γ.r - γ.t)) := by
      simp [evalEvalBC, Polynomial.evalEval]
    refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
    obtain ⟨h', hP⟩ := he x y h
    exact exists_eq_some' hP (by rw [e0, e1, div_one]) (by rw [e0, e2, div_one])
  · intro x y h _
    obtain ⟨h', hP⟩ := he x y h
    refine ⟨_, _, h', hP, ?_⟩
    simp only [pow_zero, pow_one, eval_C, eval_mul, eval_add, eval_X, mul_one]
    ring

end Aux

section Main

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero.WeierstrassCurve"

variable {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]

abbrev Pt (W : WeierstrassCurve κ) := (W.baseChange κ).toAffine.Point

theorem strip (X₀ W : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic]
    (hWj : ∀ k : ℕ, W.j ^ p ^ (2 * k) = W.j)
    (ρ₀ : Pt W →+ Pt X₀) (hρ₀ : ρ₀ ∈ rationalHomSet κ W X₀)
    {u₀ v₀ : κ[X]} {k : ℕ} {B₀ : Set κ} (hc : IsCoprime u₀ v₀) (hw : wronskian u₀ v₀ ≠ 0) (hB : B₀.Finite)
    (hrep : XRep p ρ₀ u₀ v₀ (2 * k) B₀) :
    ∃ ρ ∈ rationalHomSet κ W X₀, ∃ (r s : κ[X]) (B : Set κ),
      IsCoprime r s ∧ wronskian r s ≠ 0 ∧ B.Finite ∧ XRep p ρ r s 0 B := by
  set σ := iterateFrobenius κ p (2 * k) with hσ
  have hρ₀0 : ρ₀ ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hB.infinite_compl.nonempty
    obtain ⟨y, hy⟩ := exists_nonsingular W x
    obtain ⟨x', y', h', hP, -⟩ := hrep x y hy hx
    rw [h0] at hP
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hP.symm

  have hFr := mapPt_iterateFrobenius_mem_rationalHomSet p W (2 * k)
  obtain ⟨y₀, hy₀⟩ := exists_nonsingular W (0 : κ)
  have hFr0 : mapPt W σ ≠ 0 := by
    intro h0
    have := congrArg (fun f => f (.some 0 y₀ hy₀)) h0
    simp only [mapPt_some, AddMonoidHom.zero_apply] at this
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ this
  have hwX : wronskian (X : κ[X]) 1 ≠ 0 := by
    rw [wronskian, derivative_one, derivative_X, mul_zero, one_mul, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  obtain ⟨ρ₁, hρ₁, hρρ₁⟩ := WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p
    W (W.map σ) X₀ hFr hρ₀ hFr0 hρ₀0 (fun T hT => by rw [mapPt_injective W σ (hT.trans (mapPt_zero W σ).symm), map_zero])
    (2 * k) (isCoprime_one_right (x := (X : κ[X]))) hwX hc hB
    (fun x y h _ => by
      obtain ⟨h₂, hP⟩ := mapPt_iterateFrobenius_some p W (2 * k) h
      exact ⟨_, _, h₂, hP, by rw [eval_one, eval_X, mul_one]⟩)
    (fun x y h hx => hrep x y h hx)

  have hpk : 0 < p ^ (2 * k) := pow_pos (Fact.out : p.Prime).pos (2 * k)
  have hrep₁ : XRep p ρ₁ u₀ v₀ 0 (σ '' B₀) := by
    intro X' Y' hR hX'
    obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq X' hpk
    obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq Y' hpk
    have h : W.toAffine.Nonsingular x y := (WeierstrassCurve.Affine.map_nonsingular W σ.injective x y).mp hR
    have hx : x ∉ B₀ := fun hb => hX' ⟨x, hb, rfl⟩
    obtain ⟨x', y', h', hP, hx'⟩ := hrep x y h hx
    refine ⟨x', y', h', ?_, by simpa only [pow_zero, pow_one] using hx'⟩
    show (ρ₁.comp (mapPt W σ)) (.some x y h) = _
    rw [← hρρ₁]
    exact hP

  have hj : W.j = (W.map σ).j := by rw [WeierstrassCurve.map_j, hσ, iterateFrobenius_def, hWj]
  obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W (W.map σ) hj
  obtain ⟨e, he, hrepe⟩ := exists_hom_of_variableChange p W (W.map σ) γ hγ
  have hu0 : (↑γ.u⁻¹ : κ) ^ 2 ≠ 0 := pow_ne_zero 2 (Units.ne_zero _)
  have hB₁ : (σ '' B₀).Finite := hB.image σ
  obtain ⟨U, V, B'', hcUV, -, hwUV, hB'', hrepUV⟩ := XRep.comp (W₃ := X₀) (isCoprime_C_right _ one_ne_zero)
    (natDegree_linear_pos (-γ.r) hu0 _) (wronskian_linear_C (-γ.r) hu0 one_ne_zero) Set.finite_empty hrepe
    hc (XRep.natDegree_pos p (W₁ := W.map σ) (W₂ := X₀) ρ₁ hc hB₁ hrep₁) hw hB₁ hrep₁
  refine ⟨ρ₁.comp e, WeierstrassCurve.comp_mem_rationalHomSet κ W (W.map σ) X₀ he hρ₁, U, V, B'', hcUV, hwUV, hB'', ?_⟩
  (first | exact hrepUV | simpa only [zero_add] using hrepUV | (have h__ := hrepUV; simp only [zero_add] at h__; exact h__))

theorem main (X₀ W : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic]
    (hss : ∀ P : X₀.toAffine.Point, p • P = 0 → P = 0)
    (χ : Pt X₀ →+ Pt W) (hχ : χ ∈ rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0) :
    ∃ ρ ∈ rationalHomSet κ W X₀, ∃ (r s : κ[X]) (B : Set κ),
      IsCoprime r s ∧ wronskian r s ≠ 0 ∧ B.Finite ∧ XRep p ρ r s 0 B := by
  have hX₀ : ∀ P : Pt X₀, p • P = 0 → P = 0 := fun P hP => hss P hP
  have hW : ∀ P : Pt W, p • P = 0 → P = 0 := noTorsion_of_hom hχ hχ0 p hX₀

  have hWj1 : W.j ^ p ^ 2 = W.j :=
    WeierstrassCurve.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero p W (fun P hP => hW P (by rwa [natCast_zsmul] at hP))
  have hWj : ∀ k, W.j ^ p ^ (2 * k) = W.j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hWj1]

  obtain ⟨σ, hσ, n, hn, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ X₀ W hχ hχ0
  have hσ0 : σ ≠ 0 := by
    intro h0
    obtain ⟨P, hP⟩ := exists_nsmul_ne_zero p X₀ hX₀ (N := n.toNat) (by omega)
    apply hP
    have h1 := hdual.comp_left P
    rw [h0, AddMonoidHom.zero_apply] at h1
    rw [← natCast_zsmul, Int.toNat_of_nonneg hn.le]
    exact h1.symm

  obtain ⟨α, hα, m, hm, hαα⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_comp_self_add_char_mul_sq_smul_id_eq_zero p X₀ hss
  have hααP : ∀ P : Pt X₀, α (α P) = -((p * m.natAbs ^ 2 : ℕ) • P) := by
    intro P
    have h1 := congrArg (fun f => f P) hαα
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at h1
    rw [eq_neg_iff_add_eq_zero, ← h1, ← natCast_zsmul]
    congr 2
    push_cast
    rw [sq_abs]
  have hM0 : p * m.natAbs ^ 2 ≠ 0 :=
    mul_ne_zero (Fact.out : p.Prime).ne_zero (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hm))
  have hα0 : α ≠ 0 := by
    intro h0
    obtain ⟨P, hP⟩ := exists_nsmul_ne_zero p X₀ hX₀ hM0
    have h1 := hααP P
    rw [h0, AddMonoidHom.zero_apply] at h1
    have h2 : (0 : Pt X₀) = -((p * m.natAbs ^ 2) • P) := h1
    rw [zero_eq_neg] at h2
    exact hP h2
  obtain ⟨uα, vα, eα, Bα, hcα, hwα, hBα, hrepα⟩ := exists_XRep_wronskian (p := p) (W₁ := X₀) (W₂ := X₀) α hα hα0
  have hodd : Odd eα := odd_of_comp_self_eq p X₀ hss hm hααP hcα hwα hBα hrepα

  obtain ⟨uσ, vσ, eσ, Bσ, hcσ, hwσ, hBσ, hrepσ⟩ := exists_XRep_wronskian (p := p) (W₁ := W) (W₂ := X₀) σ hσ hσ0
  rcases Nat.even_or_odd eσ with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact strip p X₀ W hWj σ hσ hcσ hwσ hBσ (k := k) (by rw [two_mul, ← hk]; exact hrepσ)
  · obtain ⟨j, hj⟩ := hodd
    obtain ⟨U, V, B'', hcUV, -, hwUV, hB'', hrepUV⟩ := XRep.comp (W₃ := X₀) hcσ
      (XRep.natDegree_pos p (W₁ := W) (W₂ := X₀) σ hcσ hBσ hrepσ) hwσ hBσ hrepσ hcα
      (XRep.natDegree_pos p (W₁ := X₀) (W₂ := X₀) α hcα hBα hrepα) hwα hBα hrepα
    refine strip p X₀ W hWj (α.comp σ) (WeierstrassCurve.comp_mem_rationalHomSet κ W X₀ X₀ hσ hα) hcUV hwUV hB''
      (k := k + j + 1) ?_
    rw [show 2 * (k + j + 1) = eσ + eα by omega]
    exact hrepUV

end Main

end WeierstrassCurve.SeparableToSupersingular
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero.WeierstrassCurve.SeparableToSupersingular"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero.WeierstrassCurve"

open WeierstrassCurve.SeparableToSupersingular in
theorem solution
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (X₀ W : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic]
    (hss : ∀ P : X₀.toAffine.Point, p • P = 0 → P = 0)
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0) :
    ∃ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀, ∃ (r s : Polynomial κ) (B : Set κ),
      IsCoprime r s ∧ Polynomial.wronskian r s ≠ 0 ∧ B.Finite ∧
      ∀ (x y : κ) (h : (W.baseChange κ).toAffine.Nonsingular x y), x ∉ B →
        ∃ (x' y' : κ) (h' : (X₀.baseChange κ).toAffine.Nonsingular x' y'),
          ρ (.some x y h) = .some x' y' h' ∧ x' * s.eval x = r.eval x := by
  obtain ⟨ρ, hρ, r, s, B, hc, hw, hB, hrep⟩ := main p X₀ W hss χ hχ hχ0
  refine ⟨ρ, hρ, r, s, B, hc, hw, hB, fun x y h hx => ?_⟩
  obtain ⟨x', y', h', hP, hx'⟩ := hrep x y h hx
  exact ⟨x', y', h', hP, by simpa only [pow_zero, pow_one] using hx'⟩

end S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_wronskian_ne_zero_of_forall_nsmul_eq_zero (solution)
