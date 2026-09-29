-- Prove2me | solution 1 for WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5f14ebde-f2df-525e-a931-175d201f648c

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import Theorems.Thm_WeierstrassCurve_Affine_adjoin_yCoord_eq_top
import Theorems.Thm_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField_of_two_ne_zero_or
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Polynomial

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ a₃ a₁ b₂ a₄ a₂ a₆ IsIntegral b₆ Δ minimal b₄"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "FunctionField polynomial yCoord weierstrassQuadratic weierstrassQuadratic_sub_degree_lt weierstrassQuadratic_monic aeval_yCoord_weierstrassQuadratic isIntegral_yCoord adjoin_yCoord_eq_top finiteDimensional_ratFunc_functionField"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {F : Type*} [Field F] {W : Affine F}

theorem natDegree_weierstrassQuadratic : (weierstrassQuadratic W).natDegree = 2 := by
  rw [weierstrassQuadratic, Polynomial.natDegree_add_eq_left_of_degree_lt]
  · exact Polynomial.natDegree_X_pow 2
  · rw [Polynomial.degree_X_pow]
    exact weierstrassQuadratic_sub_degree_lt

theorem natDegree_minpoly_yCoord_le' :
    (minpoly (RatFunc F) (yCoord W)).natDegree ≤ 2 := by
  have hdvd : minpoly (RatFunc F) (yCoord W) ∣ weierstrassQuadratic W :=
    minpoly.dvd _ _ aeval_yCoord_weierstrassQuadratic
  exact (Polynomial.natDegree_le_of_dvd hdvd weierstrassQuadratic_monic.ne_zero).trans
    natDegree_weierstrassQuadratic.le

theorem derivative_weierstrassQuadratic :
    derivative (weierstrassQuadratic W)
      = C (2 : RatFunc F) * X + C (algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃)) := by
  rw [weierstrassQuadratic, derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X,
    derivative_C, sub_zero]
  norm_num

theorem coeff_derivative_weierstrassQuadratic_zero :
    (derivative (weierstrassQuadratic W)).coeff 0
      = algebraMap F[X] (RatFunc F) (C W.a₁ * X + C W.a₃) := by
  rw [derivative_weierstrassQuadratic, coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add, coeff_C_zero]

theorem isSeparable_yCoord_of_or (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    IsSeparable (RatFunc F) (yCoord W) := by
  have hint : _root_.IsIntegral (RatFunc F) (yCoord W) := isIntegral_yCoord
  set m := minpoly (RatFunc F) (yCoord W) with hm
  have hirr : Irreducible m := minpoly.irreducible hint
  have hmon : m.Monic := minpoly.monic hint
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hint
  have hle : m.natDegree ≤ 2 := natDegree_minpoly_yCoord_le'

  have hcoeff : (derivative m).coeff (m.natDegree - 1) = (m.natDegree : RatFunc F) := by
    have h1 : m.natDegree - 1 + 1 = m.natDegree := by omega
    rw [Polynomial.coeff_derivative, h1, hmon.coeff_natDegree, one_mul]
    have : ((m.natDegree - 1 : ℕ) : RatFunc F) + 1 = (m.natDegree : RatFunc F) := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, h1]
    exact this
  have hder : derivative m ≠ 0 := by
    intro h0
    interval_cases hn : m.natDegree
    ·
      have := hcoeff
      rw [h0, Polynomial.coeff_zero] at this
      exact one_ne_zero (by exact_mod_cast this.symm)
    ·
      rcases h with h2 | h13
      · have h2' : (2 : RatFunc F) ≠ 0 := by
          rw [← map_ofNat (algebraMap F (RatFunc F)) 2]
          exact (_root_.map_ne_zero _).mpr h2
        have := hcoeff
        rw [h0, Polynomial.coeff_zero] at this
        exact h2' (by exact_mod_cast this.symm)
      · have hmQ : m = weierstrassQuadratic W :=
          (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon weierstrassQuadratic_monic
            (minpoly.dvd _ _ aeval_yCoord_weierstrassQuadratic)
            (by rw [natDegree_weierstrassQuadratic, hn])).symm
        have hc := coeff_derivative_weierstrassQuadratic_zero (W := W)
        rw [← hmQ, h0, Polynomial.coeff_zero] at hc
        have hpoly : (C W.a₁ * X + C W.a₃ : F[X]) ≠ 0 := by
          intro hz
          rcases h13 with h1 | h3
          · apply h1
            simpa using congrArg (fun p : F[X] => p.coeff 1) hz
          · apply h3
            simpa using congrArg (fun p : F[X] => p.coeff 0) hz
        exact hpoly ((map_eq_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mp hc.symm)
  show m.Separable
  exact (Polynomial.separable_iff_derivative_ne_zero hirr).mpr hder

theorem algebra_isSeparable_ratFunc_functionField_of_or (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    Algebra.IsSeparable (RatFunc F) W.FunctionField := by
  have h1 : Algebra.IsSeparable (RatFunc F)
      (IntermediateField.adjoin (RatFunc F) ({yCoord W} : Set W.FunctionField)) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
        (F := RatFunc F) (E := W.FunctionField)).mpr
      (isSeparable_yCoord_of_or h)
  rw [adjoin_yCoord_eq_top] at h1
  exact AlgEquiv.Algebra.isSeparable
    (IntermediateField.topEquiv (F := RatFunc F) (E := W.FunctionField))

theorem hasPrincipalDivisors_functionField_of_two_ne_zero_or' (W : Affine F)
    (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField := by
  haveI : FiniteDimensional (RatFunc F) W.FunctionField := finiteDimensional_ratFunc_functionField W
  haveI : Algebra.IsSeparable (RatFunc F) W.FunctionField :=
    algebra_isSeparable_ratFunc_functionField_of_or h
  exact AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable F W.FunctionField

theorem two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero' (W : Affine F) (hΔ : W.Δ ≠ 0) :
    (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h2, h1, h3⟩ := h
  apply hΔ
  have hb2 : W.b₂ = 0 := by
    rw [WeierstrassCurve.b₂, h1]; linear_combination (2 * W.a₂) * h2
  have hb4 : W.b₄ = 0 := by
    rw [WeierstrassCurve.b₄, h1]; linear_combination W.a₄ * h2
  have hb6 : W.b₆ = 0 := by
    rw [WeierstrassCurve.b₆, h3]; linear_combination (2 * W.a₆) * h2
  rw [WeierstrassCurve.Δ, hb2, hb4, hb6]; ring

theorem hasPrincipalDivisors_functionField_of_isElliptic' (W : Affine F) [W.IsElliptic] :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField :=
  hasPrincipalDivisors_functionField_of_two_ne_zero_or' W
    (two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero' W W.isUnit_Δ.ne_zero)

end WeierstrassCurve.Affine

end

theorem solution
    {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)
    (h : (2 : F) ≠ 0 ∨ W.a₁ ≠ 0 ∨ W.a₃ ≠ 0) :
    AlgebraicCurve.HasPrincipalDivisors F W.FunctionField :=
  WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or' W h

end S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField_of_two_ne_zero_or
end P2MW
export P2MW.S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField_of_two_ne_zero_or (solution)
