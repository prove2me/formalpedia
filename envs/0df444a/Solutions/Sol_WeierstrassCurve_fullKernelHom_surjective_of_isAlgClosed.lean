-- Prove2me | solution 1 for WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bc5c8dca-3297-5f95-a25e-31712799f835

import Mathlib

import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap

import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_GenusOnePic0
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_abelTheorem
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom
import Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
import Theorems.Thm_Algebra_IsSeparable_of_coprime_finrank_expChar
import Theorems.Thm_WeierstrassCurve_Affine_pointMapOfPushforward_surjective_of_separableAlong
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Theorems.Thm_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed.WeierstrassCurve WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY mk.injEq a₃ a₁ map mk a₂ Affine.Point.some Affine.negAddY Affine.Point.zero_def IsIntegral toAffine Affine.Point Affine.addX ψ₂ Affine.Point.some_ne_zero Δ Affine.addY Affine.Y_eq_of_X_eq Affine.equation_iff j fullKernelQuotient fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet fullKernelQuotient_two oddOrderSummingSet veluGx veluGy veluT veluU veluQuotient veluQuotient2 veluX veluY Affine.exists_genusOnePlaceGate_isCentred_abelTheorem veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq Affine.hasPrincipalDivisors_of_isAlgClosed exists_veluPointHom_oddOrderSummingSet_of_ringHom exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed Affine.pointMapOfPushforward_surjective_of_separableAlong velu2X velu2Y veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne exists_addMonoidHom_coe_eq_veluPointMap2 veluPointMap2_surjective_of_isAlgClosed fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2 fullKernelQuotient_discriminant_ne_zero"
p2m_open "WeierstrassCurve"

private def homOfEq {K : Type*} [Field K] [DecidableEq K] :
    ∀ {W V : WeierstrassCurve K}, W = V → (W.toAffine.Point →+ V.toAffine.Point)
  | _, _, rfl => AddMonoidHom.id _

private theorem homOfEq_coordsOrZero {K : Type*} [Field K] [DecidableEq K] {W V : WeierstrassCurve K} (h : W = V)
    (P : W.toAffine.Point) : (homOfEq h P).coordsOrZero = P.coordsOrZero := by
  subst h; rfl

private theorem ker_homOfEq {K : Type*} [Field K] [DecidableEq K] {W V : WeierstrassCurve K} (h : W = V) :
    (homOfEq h).ker = ⊥ := by
  subst h
  ext P
  simp [homOfEq]

section Transport
variable {K : Type*} [Field K] [DecidableEq K]

end Transport

section TorsionImage
variable {K : Type*} [Field K] [DecidableEq K]
end TorsionImage

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

private theorem sum_Icc_two_mul_eq_sum_pairs {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * n), f k = ∑ k ∈ Finset.Icc 1 n, (f k + f (2 * n + 1 - k)) := by
  rw [Finset.sum_add_distrib]
  have hsplit : Finset.Icc 1 (2 * n) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (2 * n) := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (2 * n)) := by
    rw [Finset.disjoint_left]; intro k hk hk'; simp only [Finset.mem_Icc] at hk hk'; omega
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  refine Finset.sum_nbij' (fun k => 2 * n + 1 - k) (fun k => 2 * n + 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; congr 1; omega

private theorem fullKernelPin_eq_veluXY_of_odd
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    {x y : F} (h : W.toAffine.Nonsingular x y)
    (hP : (Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    (x + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
        (((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
     y + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
        (((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) =
      (W.veluX (W.oddOrderSummingSet Q n) x, W.veluY (W.oddOrderSummingSet Q n) x y) := by
  classical
  have h2n : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel (2 * n) 1
  have hord : (2 * n + 1) • Q = 0 := hQ ▸ addOrderOf_nsmul_eq_zero Q
  have hrefl : ∀ k, k ≤ 2 * n + 1 → (2 * n + 1 - k) • Q = -(k • Q) := by
    intro k hk
    rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hk, hord]

  have haff : ∀ k, 1 ≤ k → k ≤ 2 * n →
      ∃ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀), k • Q = Point.some x₀ y₀ h₀ ∧ x ≠ x₀ := by
    intro k hk1 hk2
    have hne : k • Q ≠ 0 := _root_.nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
    rcases hkQ : k • Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hkQ hne
    · refine ⟨x₀, y₀, h₀, rfl, ?_⟩
      intro hxx
      apply hP
      rcases Affine.Y_eq_of_X_eq h.1 h₀.1 hxx with hyy | hyy
      · have hPt : (Point.some x y h : W.toAffine.Point) = k • Q := by
          rw [hkQ]; subst hxx; subst hyy; rfl
        rw [hPt]
        exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k
      · have hPt : (Point.some x y h : W.toAffine.Point) = -(k • Q) := by
          rw [hkQ, Point.neg_some]; subst hxx; subst hyy; rfl
        rw [hPt]
        exact AddSubgroup.neg_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)

  have hpair : ∀ k ∈ Finset.Icc 1 n,
      ((((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1)
        + (((Point.some x y h : W.toAffine.Point) + (2 * n + 1 - k) • Q).coordsOrZero.1
            - ((2 * n + 1 - k) • Q).coordsOrZero.1)
        = W.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 / (x - (k • Q).coordsOrZero.1)
          + W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 / (x - (k • Q).coordsOrZero.1) ^ 2) ∧
      ((((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)
        + (((Point.some x y h : W.toAffine.Point) + (2 * n + 1 - k) • Q).coordsOrZero.2
            - ((2 * n + 1 - k) • Q).coordsOrZero.2)
        = -(W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 * (2 * y + W.a₁ * x + W.a₃)
              / (x - (k • Q).coordsOrZero.1) ^ 3
            + W.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
              * (W.a₁ * (x - (k • Q).coordsOrZero.1) + y - (k • Q).coordsOrZero.2)
              / (x - (k • Q).coordsOrZero.1) ^ 2
            + (W.a₁ * W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
                - W.veluGx (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
                  * W.veluGy (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2)
              / (x - (k • Q).coordsOrZero.1) ^ 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨x₀, y₀, h₀, hkQ, hx⟩ := haff k hk.1 (by omega)
    rw [hrefl k (by omega), hkQ]
    exact W.velu_pair h h₀ hx

  have hinj : ∀ k ∈ Finset.Icc 1 n, ∀ k' ∈ Finset.Icc 1 n,
      (k • Q).coordsOrZero = (k' • Q).coordsOrZero → k = k' := by
    intro k hk k' hk' hkk
    rw [Finset.mem_Icc] at hk hk'
    obtain ⟨x₀, y₀, h₀, hkQ, -⟩ := haff k hk.1 (by omega)
    obtain ⟨x₁, y₁, h₁, hk'Q, -⟩ := haff k' hk'.1 (by omega)
    have hpt : k • Q = k' • Q := by
      rw [hkQ, hk'Q] at hkk ⊢
      simp only [Point.coordsOrZero_some, Prod.mk.injEq] at hkk
      obtain ⟨rfl, rfl⟩ := hkk
      rfl
    have hmod := (nsmul_inj_mod (x := Q)).mp hpt
    rwa [hQ, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod

  rw [h2n]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [sum_Icc_two_mul_eq_sum_pairs, Finset.sum_congr rfl (fun k hk => (hpair k hk).1)]
    simp only [veluX, oddOrderSummingSet, Finset.sum_image hinj]
  · dsimp only
    rw [sum_Icc_two_mul_eq_sum_pairs, Finset.sum_congr rfl (fun k hk => (hpair k hk).2)]
    simp only [veluY, oddOrderSummingSet, Finset.sum_image hinj, Finset.sum_neg_distrib, sub_eq_add_neg]

end WeierstrassCurve

open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point AlgebraicCurve in
/-!                                                                                           -/
noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY mk.injEq a₃ a₁ map mk a₂ Affine.Point.some Affine.negAddY Affine.Point.zero_def IsIntegral toAffine Affine.Point Affine.addX ψ₂ Affine.Point.some_ne_zero Δ Affine.addY Affine.Y_eq_of_X_eq Affine.equation_iff j fullKernelQuotient fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet fullKernelQuotient_two oddOrderSummingSet veluGx veluGy veluT veluU veluQuotient veluQuotient2 veluX veluY Affine.exists_genusOnePlaceGate_isCentred_abelTheorem veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq Affine.hasPrincipalDivisors_of_isAlgClosed exists_veluPointHom_oddOrderSummingSet_of_ringHom exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed Affine.pointMapOfPushforward_surjective_of_separableAlong velu2X velu2Y veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne exists_addMonoidHom_coe_eq_veluPointMap2 veluPointMap2_surjective_of_isAlgClosed fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2 fullKernelQuotient_discriminant_ne_zero"
namespace OddVeluSeam
p2m_open "WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point AlgebraicCurve"

universe u

variable {F : Type u} [Field F] [DecidableEq F]
variable {V W : Affine F} [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

omit [DecidableEq F] [AbelTheorem V] [AbelTheorem W] in

private theorem inertiaDegAlong_eq_one' (w : AlgebraicCurve.Place F W.FunctionField) :
    w.inertiaDegAlong ι hι = 1 := by
  have h := AlgebraicCurve.Place.deg_restrictAlong_mul_inertiaDegAlong ι hι w
  rw [GenusOnePlaceGate.deg_eq_one (W := V) (w.restrictAlong ι hι),
    GenusOnePlaceGate.deg_eq_one (W := W) w, one_mul] at h
  exact h

omit [DecidableEq F] [AbelTheorem V] [AbelTheorem W] in
private theorem pushforwardAlong_single_eq' (w : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    Divisor.pushforwardAlong ι hι (Finsupp.single w n) = Finsupp.single (w.restrictAlong ι hι) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one' ι hι w, Nat.cast_one, mul_one]

variable (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)

omit [AbelTheorem V] [AbelTheorem W] in
private theorem pushforwardAlongDegZero_pointDivisor' {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongDegZero ι hι (pointDivisor P) = pointDivisor Q := by
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, coe_pointDivisor, map_sub,
    pushforwardAlong_single_eq' ι hι, pushforwardAlong_single_eq' ι hι, hP, h0]

omit [AbelTheorem V] [AbelTheorem W] in
private theorem pushforwardAlongHom_pointClass' {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P) = pointClass Q := by
  show Pic0.pushforwardAlongHom ι hι hfin hN (Pic0.mk (pointDivisor P)) = Pic0.mk (pointDivisor Q)
  rw [Pic0.pushforwardAlongHom_mk, pushforwardAlongDegZero_pointDivisor' ι hι hP h0]

private theorem pointMapOfPushforward_apply' (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = genusOnePic0Equiv V (Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P)) := by
  rw [← genusOnePic0Equiv_symm_apply]
  rfl

private theorem pointMapOfPushforward_eq_of_seam' (g : W.Point → V.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P)) (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P = g P := by
  rw [pointMapOfPushforward_apply',
    pushforwardAlongHom_pointClass' ι hι hfin hN (hg P) ((hg 0).trans (by rw [hg0])),
    genusOnePic0Equiv_apply, pic0ToPoint_pointClass]

end WeierstrassCurve.OddVeluSeam

end

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY mk.injEq a₃ a₁ map mk a₂ Affine.Point.some Affine.negAddY Affine.Point.zero_def IsIntegral toAffine Affine.Point Affine.addX ψ₂ Affine.Point.some_ne_zero Δ Affine.addY Affine.Y_eq_of_X_eq Affine.equation_iff j fullKernelQuotient fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet fullKernelQuotient_two oddOrderSummingSet veluGx veluGy veluT veluU veluQuotient veluQuotient2 veluX veluY Affine.exists_genusOnePlaceGate_isCentred_abelTheorem veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq Affine.hasPrincipalDivisors_of_isAlgClosed exists_veluPointHom_oddOrderSummingSet_of_ringHom exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed Affine.pointMapOfPushforward_surjective_of_separableAlong velu2X velu2Y veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne exists_addMonoidHom_coe_eq_veluPointMap2 veluPointMap2_surjective_of_isAlgClosed fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2 fullKernelQuotient_discriminant_ne_zero"
p2m_open "WeierstrassCurve"

open WeierstrassCurve.Affine.Point AlgebraicCurve WeierstrassCurve.OddVeluSeam in
private theorem exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed_odd
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hnF : ((2 * n + 1 : ℕ) : F) ≠ 0)
    (Q : W.toAffine.Point) (hord : addOrderOf Q = 2 * n + 1) :
    let S := W.oddOrderSummingSet Q n
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') ∧
      Function.Surjective φ := by
  intro S
  classical
  have hΔ' : (W.veluQuotient S).Δ ≠ 0 :=
    veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq W n Q hord
  haveI hVell : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
  haveI : (W.veluQuotient S).toAffine.IsElliptic := hVell
  haveI : W.toAffine.IsElliptic := ‹W.IsElliptic›

  haveI : IsDedekindDomain W.toAffine.CoordinateRing := CoordinateRing.isDedekindDomain W
  haveI : IsDedekindDomain (W.veluQuotient S).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient S)
  haveI : HasPrincipalDivisors F W.toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed W.toAffine
  haveI : HasPrincipalDivisors F (W.veluQuotient S).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed (W.veluQuotient S).toAffine
  obtain ⟨gW, cW, aW⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem W.toAffine
  obtain ⟨gV, cV, aV⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem (W.veluQuotient S).toAffine
  letI : GenusOnePlaceGate W.toAffine := gW
  haveI : GenusOnePlaceGate.IsCentred W.toAffine := cW
  haveI : AbelTheorem W.toAffine := aW
  letI : GenusOnePlaceGate (W.veluQuotient S).toAffine := gV
  haveI : GenusOnePlaceGate.IsCentred (W.veluQuotient S).toAffine := cV
  haveI : AbelTheorem (W.veluQuotient S).toAffine := aV

  obtain ⟨ι, hι, hfin, hdeg, hker, hzero, haff⟩ :=
    exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed (W := W) hord hΔ'

  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI : Module.Finite (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField := hfin
    obtain ⟨q, hq⟩ := ExpChar.exists F
    haveI : ExpChar (W.veluQuotient S).toAffine.FunctionField q :=
      expChar_of_injective_algebraMap (algebraMap F _).injective q
    have hcop : Nat.Coprime
        (Module.finrank (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField) q := by
      have hfr : Module.finrank (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField
          = 2 * n + 1 := hdeg
      rw [hfr]
      rcases hq with _ | ⟨hqprime⟩
      · exact Nat.coprime_one_right _
      · refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqprime).mpr fun hdvd => hnF ?_))
        exact (CharP.cast_eq_zero_iff F q _).mpr hdvd
    exact Algebra.IsSeparable.of_coprime_finrank_expChar _ _ q hcop

  have hN : NormFormulaAlong F ι hfin := normFormulaAlong_of_separableAlong ι hfin hsep

  let g : W.toAffine.Point → (W.veluQuotient S).toAffine.Point := fun P =>
    match P with
    | 0 => 0
    | .some a b hab =>
        if hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q then 0
        else .some _ _ (Classical.choose (haff a b hab hm))
  have hg0 : g 0 = 0 := rfl
  have hgseam : ∀ P : W.toAffine.Point, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P) := by
    intro P
    cases P with
    | zero => exact hzero _ (AddSubgroup.zero_mem _)
    | some a b hab =>
        by_cases hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q
        · have : g (.some a b hab) = 0 := by simp only [g, dif_pos hm]
          rw [this]; exact hzero _ hm
        · have : g (.some a b hab) = .some _ _ (Classical.choose (haff a b hab hm)) := by
            simp only [g, dif_neg hm]
          rw [this]; exact Classical.choose_spec (haff a b hab hm)

  refine ⟨pointMapOfPushforward ι hι hfin hN, ?_, ?_,
    WeierstrassCurve.Affine.pointMapOfPushforward_surjective_of_separableAlong
      W.toAffine (W.veluQuotient S).toAffine ι hι hfin hsep hN⟩
  · ext P
    rw [AddMonoidHom.mem_ker, pointMapOfPushforward_eq_of_seam' ι hι hfin hN g hg0 hgseam P]
    cases P with
    | zero => exact ⟨fun _ => AddSubgroup.zero_mem _, fun _ => rfl⟩
    | some a b hab =>
        by_cases hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q
        · simp only [g, dif_pos hm]; exact ⟨fun _ => hm, fun _ => trivial⟩
        · simp only [g, dif_neg hm]
          exact ⟨fun h0 => (Point.some_ne_zero _ h0).elim, fun h0 => absurd h0 hm⟩
  · intro x y h hP
    obtain ⟨h', _⟩ := haff x y h hP
    refine ⟨h', ?_⟩
    rw [pointMapOfPushforward_eq_of_seam' ι hι hfin hN g hg0 hgseam (.some x y h)]
    simp only [g, dif_neg hP]
    rfl

private theorem exists_veluPointHom_oddOrderSummingSet_of_odd
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hnF : ((2 * n + 1 : ℕ) : F) ≠ 0)
    (Q : W.toAffine.Point) (hord : addOrderOf Q = 2 * n + 1) :
    let S := W.oddOrderSummingSet Q ((2 * n + 1) / 2)
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') := by
  classical
  refine exists_veluPointHom_oddOrderSummingSet_of_ringHom (algebraMap F (AlgebraicClosure F)) W Q hord ?_
  intro W' _ Q' hQ'
  have hnL : ((2 * ((2 * n + 1) / 2) + 1 : ℕ) : AlgebraicClosure F) ≠ 0 := by
    have h2 : 2 * ((2 * n + 1) / 2) + 1 = 2 * n + 1 := by omega
    rw [h2]
    intro h0
    apply hnF
    apply (algebraMap F (AlgebraicClosure F)).injective
    rw [map_natCast, h0, map_zero]
  obtain ⟨φ', h1, h2, -⟩ :=
    exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed_odd W' hnL Q' (hQ'.trans (by omega))
  exact ⟨φ', h1, h2⟩

private theorem ker_homOfEq_comp {K : Type*} [Field K] [DecidableEq K] {W V U : WeierstrassCurve K} (h : V = U)
    (f : W.toAffine.Point →+ V.toAffine.Point) : ((homOfEq h).comp f).ker = f.ker := by
  subst h
  ext P
  exact Iff.rfl

private theorem exists_fullKernelHom_of_odd
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hN : (N : F) ≠ 0) (hodd : Odd N) (Q : W.toAffine.Point) (hQ : addOrderOf Q = N) :
    ∃ φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
        (φ P).coordsOrZero =
          (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
              ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
           P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
              ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) := by
  classical
  obtain ⟨m, rfl⟩ := hodd
  have hm : (2 * m + 1) / 2 = m := by omega
  have key := exists_veluPointHom_oddOrderSummingSet_of_odd W hN Q hQ
  rw [hm] at key
  obtain ⟨φ₀, hker₀, hpin₀⟩ := key
  have hcurve : W.fullKernelQuotient Q (2 * m + 1) = W.veluQuotient (W.oddOrderSummingSet Q m) :=
    fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet W Q m hQ
  refine ⟨(homOfEq hcurve.symm).comp φ₀, ?_, ?_⟩
  · rw [ker_homOfEq_comp, hker₀]
  · intro P hP
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd (AddSubgroup.zero_mem _) hP
    · obtain ⟨h', hφ₀⟩ := hpin₀ x y h hP
      rw [AddMonoidHom.comp_apply, homOfEq_coordsOrZero, hφ₀, Point.coordsOrZero_some]
      exact (fullKernelPin_eq_veluXY_of_odd W Q m hQ h hP).symm

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

private theorem addOrderOf_veluPointMap2_eq {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {m : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1))
    {x₀ y₀ : F} {h₀ : W.toAffine.Nonsingular x₀ y₀}
    (hT : (m + 1) • Q = Affine.Point.some x₀ y₀ h₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    addOrderOf (veluPointMap2 h2 h₀.1 hgy hΔ Q) = m + 1 := by
  obtain ⟨φ, hφ⟩ := W.exists_addMonoidHom_coe_eq_veluPointMap2 h2 h₀.1 hgy hΔ
  rw [← hφ]
  have hne : ∀ k, 0 < k → k < 2 * (m + 1) → k • Q ≠ 0 := fun k hk1 hk2 =>
    _root_.nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; exact hk2)

  have hcoords : ∀ i, i < m → ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      (i + 1) • Q = Affine.Point.some x y h ∧ x ≠ x₀ := by
    intro i hi
    rcases hP : (i + 1) • Q with _ | ⟨x, y, h⟩
    · exact absurd (hP.trans Affine.Point.zero_def.symm) (hne (i + 1) (by omega) (by omega))
    · refine ⟨x, y, h, rfl, fun hx => ?_⟩
      subst hx
      have hPT : (i + 1) • Q = (m + 1) • Q := by
        rw [hP, hT, W.some_eq_of_X_eq_of_veluGy_eq_zero' h₀ hgy h]
      have := nsmul_injOn_Iio_addOrderOf (x := Q) (by simp only [Set.mem_Iio]; omega)
        (by simp only [Set.mem_Iio]; omega) hPT
      omega

  have hzero : (m + 1) • φ Q = 0 := by
    rw [← map_nsmul φ (m + 1) Q, hT, hφ, veluPointMap2_some_of_eq h2 h₀.1 hgy hΔ h₀ rfl]
    rfl
  have hfin : IsOfFinAddOrder (φ Q) :=
    φ.isOfFinAddOrder (addOrderOf_pos_iff.mp (by rw [hQ]; omega))
  have hk : 0 < addOrderOf (φ Q) := addOrderOf_pos_iff.mpr hfin
  have hdvd : addOrderOf (φ Q) ∣ m + 1 := addOrderOf_dvd_of_nsmul_eq_zero hzero
  have hle : addOrderOf (φ Q) ≤ m + 1 := Nat.le_of_dvd (by omega) hdvd

  have hgt : m < addOrderOf (φ Q) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, y, h, hP, hx⟩ := hcoords (addOrderOf (φ Q) - 1) (by omega)
    have h0 : (addOrderOf (φ Q) - 1 + 1) • φ Q = 0 := by
      rw [Nat.sub_add_cancel hk, addOrderOf_nsmul_eq_zero]
    rw [← map_nsmul φ (addOrderOf (φ Q) - 1 + 1) Q, hP, hφ,
      veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ h hx] at h0
    exact Affine.Point.some_ne_zero _ h0
  omega

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

private theorem sum_Icc_even_split {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1), g k
      = g (m + 1) + ∑ j ∈ Finset.Icc 1 m, (g j + g (j + (m + 1))) := by
  rw [Finset.sum_add_distrib]
  have h1 : Finset.Icc 1 (2 * (m + 1) - 1)
      = Finset.Icc 1 m ∪ ({m + 1} ∪ Finset.Icc (m + 2) (2 * m + 1)) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
    omega
  have hd1 : Disjoint (Finset.Icc 1 m) ({m + 1} ∪ Finset.Icc (m + 2) (2 * m + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at hk hk'
    omega
  have hd2 : Disjoint ({m + 1} : Finset ℕ) (Finset.Icc (m + 2) (2 * m + 1)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_Icc, Finset.mem_singleton] at hk hk'
    omega
  rw [h1, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
  have h3 : ∑ k ∈ Finset.Icc (m + 2) (2 * m + 1), g k = ∑ j ∈ Finset.Icc 1 m, g (j + (m + 1)) := by
    refine Finset.sum_nbij' (fun k => k - (m + 1)) (fun j => j + (m + 1)) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; beta_reduce; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; beta_reduce; congr 1; omega
  rw [h3]
  abel

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

private theorem _root_.WeierstrassCurve.fullKernelHom_comp_two_pinned
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] {m : ℕ}
    (h2 : (2 : F) ≠ 0) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1))
    {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀) (hT : (m + 1) • Q = Point.some x₀ y₀ h₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ₂ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (φ₂ : W.toAffine.Point →+ (W.veluQuotient2 x₀ y₀).toAffine.Point)
    (hφ₂ : ⇑φ₂ = veluPointMap2 h2 h₀.1 hgy hΔ₂)
    (ψ : (W.veluQuotient2 x₀ y₀).toAffine.Point →+
      ((W.veluQuotient2 x₀ y₀).fullKernelQuotient (φ₂ Q) (m + 1)).toAffine.Point)
    (hψker : ψ.ker = AddSubgroup.zmultiples (φ₂ Q))
    (hψpin : ∀ P : (W.veluQuotient2 x₀ y₀).toAffine.Point, P ∉ AddSubgroup.zmultiples (φ₂ Q) →
      (ψ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (m + 1 - 1),
            ((P + k • φ₂ Q).coordsOrZero.1 - (k • φ₂ Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (m + 1 - 1),
            ((P + k • φ₂ Q).coordsOrZero.2 - (k • φ₂ Q).coordsOrZero.2)))
    (hcomp : W.fullKernelQuotient Q (2 * (m + 1))
      = (W.veluQuotient2 x₀ y₀).fullKernelQuotient (φ₂ Q) (m + 1)) :
    ((homOfEq hcomp.symm).comp (ψ.comp φ₂)).ker = AddSubgroup.zmultiples Q ∧
    ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      ((homOfEq hcomp.symm).comp (ψ.comp φ₂) P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) := by
  classical
  have hφ₂app : ∀ R, φ₂ R = veluPointMap2 h2 h₀.1 hgy hΔ₂ R := fun R => congrFun hφ₂ R
  have hTc1 : ((m + 1) • Q).coordsOrZero.1 = x₀ := by rw [hT, Point.coordsOrZero_some]
  have hTc2 : ((m + 1) • Q).coordsOrZero.2 = y₀ := by rw [hT, Point.coordsOrZero_some]

  have hkerP : ∀ P : W.toAffine.Point,
      φ₂ P ∈ AddSubgroup.zmultiples (φ₂ Q) → P ∈ AddSubgroup.zmultiples Q := by
    intro P hPm
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hPm
    have h0 : veluPointMap2 h2 h₀.1 hgy hΔ₂ (P - k • Q) = 0 := by
      rw [← hφ₂app, map_sub, map_zsmul, hk, sub_self]
    rcases eq_zero_or_eq_of_veluPointMap2_eq_zero h2 h₀ hgy hΔ₂ _ h0 with h | h
    · rw [sub_eq_zero] at h
      rw [h]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples Q) k
    · rw [← hT, sub_eq_iff_eq_add] at h
      rw [h]
      exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) _)
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)

  have hstep : ∀ R : W.toAffine.Point, R ≠ 0 → R ≠ Point.some x₀ y₀ h₀ →
      (φ₂ R).coordsOrZero =
        (R.coordsOrZero.1 + ((R + Point.some x₀ y₀ h₀).coordsOrZero.1 - x₀),
         R.coordsOrZero.2 + ((R + Point.some x₀ y₀ h₀).coordsOrZero.2 - y₀)) := by
    intro R hR0 hRT
    rcases R with _ | ⟨x, y, h⟩
    · exact absurd rfl hR0
    · have hx : x ≠ x₀ := fun hx => hRT (by
        subst hx
        exact W.some_eq_of_X_eq_of_veluGy_eq_zero' h₀ hgy h)
      rw [hφ₂app, veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ₂ h hx]
      obtain ⟨e1, e2⟩ := W.velu2_translate h2 h h₀ hgy hx
      simp only [Point.coordsOrZero_some]
      rw [e1, e2]
  refine ⟨?_, ?_⟩
  · ext P
    rw [ker_homOfEq_comp]
    show ψ (φ₂ P) = 0 ↔ P ∈ AddSubgroup.zmultiples Q
    rw [← AddMonoidHom.mem_ker, hψker]
    refine ⟨hkerP P, fun hP => ?_⟩
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hP
    rw [← hk, map_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) k
  · intro P hP
    have hP0 : P ≠ 0 := fun h => hP (by rw [h]; exact AddSubgroup.zero_mem _)
    have hPT : P ≠ Point.some x₀ y₀ h₀ := fun h => hP (by
      rw [h, ← hT]; exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) _)
    have hP2 : φ₂ P ∉ AddSubgroup.zmultiples (φ₂ Q) := fun h => hP (hkerP P h)
    have hsummand : ∀ j ∈ Finset.Icc 1 m,
        ((φ₂ (P + j • Q)).coordsOrZero.1 - (φ₂ (j • Q)).coordsOrZero.1
          = ((P + j • Q).coordsOrZero.1 - (j • Q).coordsOrZero.1)
            + ((P + (j + (m + 1)) • Q).coordsOrZero.1 - ((j + (m + 1)) • Q).coordsOrZero.1)) ∧
        ((φ₂ (P + j • Q)).coordsOrZero.2 - (φ₂ (j • Q)).coordsOrZero.2
          = ((P + j • Q).coordsOrZero.2 - (j • Q).coordsOrZero.2)
            + ((P + (j + (m + 1)) • Q).coordsOrZero.2 - ((j + (m + 1)) • Q).coordsOrZero.2)) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hjQ0 : j • Q ≠ 0 := _root_.nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
      have hjQT : j • Q ≠ Point.some x₀ y₀ h₀ := by
        rw [← hT]
        intro hjT
        have := nsmul_injOn_Iio_addOrderOf (x := Q) (by simp only [Set.mem_Iio]; rw [hQ]; omega)
          (by simp only [Set.mem_Iio]; rw [hQ]; omega) hjT
        omega
      have hPj0 : P + j • Q ≠ 0 := fun h0 => hP (by
        rw [add_eq_zero_iff_eq_neg.mp h0]
        exact AddSubgroup.neg_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) j))
      have hPjT : P + j • Q ≠ Point.some x₀ y₀ h₀ := fun h0 => hP (by
        rw [← hT] at h0
        rw [eq_sub_of_add_eq h0]
        exact AddSubgroup.sub_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) _)
          (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) _))
      have hadd1 : P + j • Q + Point.some x₀ y₀ h₀ = P + (j + (m + 1)) • Q := by
        rw [← hT]; simp only [add_nsmul, one_nsmul, add_assoc]
      have hadd2 : j • Q + Point.some x₀ y₀ h₀ = (j + (m + 1)) • Q := by
        rw [← hT]; simp only [add_nsmul, one_nsmul]
      rw [hstep _ hPj0 hPjT, hstep _ hjQ0 hjQT]
      dsimp only
      rw [hadd1, hadd2]
      constructor <;> ring
    have hlead := hstep P hP0 hPT
    rw [AddMonoidHom.comp_apply, homOfEq_coordsOrZero, AddMonoidHom.comp_apply, hψpin (φ₂ P) hP2,
      Nat.add_sub_cancel]
    simp only [← map_nsmul, ← map_add]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [hlead]
      dsimp only
      rw [Finset.sum_congr rfl (fun j hj => (hsummand j hj).1), sum_Icc_even_split, hTc1, ← hT]
      ring
    · dsimp only
      rw [hlead]
      dsimp only
      rw [Finset.sum_congr rfl (fun j hj => (hsummand j hj).2), sum_Icc_even_split, hTc2, ← hT]
      ring

p2m_export "WeierstrassCurve" "fullKernelHom_comp_two_pinned"

private theorem exists_fullKernelHom_two_mul
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] {m : ℕ}
    (hN : ((2 * (m + 1) : ℕ) : F) ≠ 0) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1))
    (ih : ∀ (V : WeierstrassCurve F) [V.IsElliptic], ((m + 1 : ℕ) : F) ≠ 0 →
      ∀ (R : V.toAffine.Point), addOrderOf R = m + 1 →
        ∃ ψ : V.toAffine.Point →+ (V.fullKernelQuotient R (m + 1)).toAffine.Point,
          ψ.ker = AddSubgroup.zmultiples R ∧
          ∀ P : V.toAffine.Point, P ∉ AddSubgroup.zmultiples R →
            (ψ P).coordsOrZero =
              (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (m + 1 - 1),
                  ((P + k • R).coordsOrZero.1 - (k • R).coordsOrZero.1),
               P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (m + 1 - 1),
                  ((P + k • R).coordsOrZero.2 - (k • R).coordsOrZero.2))) :
    ∃ φ : W.toAffine.Point →+ (W.fullKernelQuotient Q (2 * (m + 1))).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
        (φ P).coordsOrZero =
          (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
              ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
           P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * (m + 1) - 1),
              ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) := by
  obtain ⟨h2, hm1, x₀, y₀, h₀, hT, hgy, hΔ₂⟩ := W.exists_two_torsion_data hN Q hQ
  haveI hE₂ : (W.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ₂⟩
  obtain ⟨φ₂, hφ₂⟩ := W.exists_addMonoidHom_coe_eq_veluPointMap2 h2 h₀.1 hgy hΔ₂
  have hQ₂ : addOrderOf (φ₂ Q) = m + 1 := by
    rw [congrFun hφ₂ Q]; exact addOrderOf_veluPointMap2_eq W h2 Q hQ hT hgy hΔ₂
  obtain ⟨ψ, hψker, hψpin⟩ := ih (W.veluQuotient2 x₀ y₀) hm1 (φ₂ Q) hQ₂
  have hcomp := fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2 W h2 Q hQ hT hgy hΔ₂
  rw [← congrFun hφ₂ Q] at hcomp
  exact ⟨_, W.fullKernelHom_comp_two_pinned h2 Q hQ h₀ hT hgy hΔ₂ φ₂ hφ₂ ψ hψker hψpin hcomp⟩

private theorem exists_fullKernelHom_all {F : Type*} [Field F] [DecidableEq F] (N : ℕ) :
    ∀ (W : WeierstrassCurve F) [W.IsElliptic], (N : F) ≠ 0 →
      ∀ (Q : W.toAffine.Point), addOrderOf Q = N →
        ∃ φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point,
          φ.ker = AddSubgroup.zmultiples Q ∧
          ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
            (φ P).coordsOrZero =
              (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
                  ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
               P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
                  ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ hN Q hQ
    have hN0 : N ≠ 0 := by
      rintro rfl
      exact hN (by simp)
    rcases Nat.even_or_odd N with heven | hodd
    · obtain ⟨r, hr⟩ := heven
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact hN0 (by simpa using hr)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr0
      have hN2 : N = 2 * (m + 1) := by omega
      subst hN2
      exact exists_fullKernelHom_two_mul W hN Q hQ
        (fun V _ hV R hR => ih (m + 1) (by omega) V hV R hR)
    · haveI : NeZero N := ⟨hN0⟩
      exact exists_fullKernelHom_of_odd W hN hodd Q hQ

section Cancel
variable {K : Type*} [Field K] [DecidableEq K]
omit [DecidableEq K] in
private lemma some_ext {W' : Affine K} {x₁ x₂ y₁ y₂ : K} {h₁ : W'.Nonsingular x₁ y₁}
    {h₂ : W'.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

end Cancel

section NatpFurniture
variable {K : Type*} [Field K] [DecidableEq K]
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

section SurjFurniture

variable {K : Type*} [Field K] [DecidableEq K]

private theorem homOfEq_surjective {W V : WeierstrassCurve K} (h : W = V) :
    Function.Surjective (homOfEq h) := by
  subst h
  exact fun P => ⟨P, rfl⟩

private theorem fullKernelHom_surjective_of_odd
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (hodd : Odd N) (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) :
    Function.Surjective φ := by
  classical
  obtain ⟨m, rfl⟩ := hodd

  obtain ⟨φ₀, hker₀, hpin₀, hsurj₀⟩ :=
    exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed_odd W hN Q hQ

  have hcar : W.veluQuotient (W.oddOrderSummingSet Q m) = W.fullKernelQuotient Q (2 * m + 1) :=
    (fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet W Q m hQ).symm
  set χ : W.toAffine.Point →+ (W.fullKernelQuotient Q (2 * m + 1)).toAffine.Point :=
    (homOfEq hcar).comp φ₀ with hχdef

  have hχker : χ.ker = AddSubgroup.zmultiples Q := by
    rw [← hker₀]
    ext P
    simp only [AddMonoidHom.mem_ker, hχdef, AddMonoidHom.comp_apply]
    constructor
    · intro h0
      have h1 : φ₀ P ∈ (homOfEq hcar).ker := AddMonoidHom.mem_ker.mpr h0
      rwa [ker_homOfEq, AddSubgroup.mem_bot] at h1
    · intro h0
      rw [h0, map_zero]

  have hagree : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero = (χ P).coordsOrZero := by
    intro P hP
    have hP0 : P ≠ 0 := fun h0 => hP (h0 ▸ AddSubgroup.zero_mem _)
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd rfl hP0
    obtain ⟨h', hval⟩ := hpin₀ x y h hP
    rw [hφ _ hP]
    show _ = ((homOfEq hcar) (φ₀ (.some x y h))).coordsOrZero
    rw [homOfEq_coordsOrZero, hval]
    have hbridge := fullKernelPin_eq_veluXY_of_odd W Q m hQ h hP
    simpa using hbridge

  have hχsurj : Function.Surjective χ := by
    have : Function.Surjective ((homOfEq hcar) ∘ φ₀) :=
      Function.Surjective.comp (homOfEq_surjective hcar) hsurj₀
    simpa [hχdef, AddMonoidHom.coe_comp] using this

  have hφχ := addMonoidHom_eq_of_ker_eq_of_coordsOrZero_eq Q φ χ hφker hχker hagree
  rw [hφχ]
  exact hχsurj

end SurjFurniture

private theorem fullKernelHom_surjective_all {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (N : ℕ) :
    ∀ (W : WeierstrassCurve K) [W.IsElliptic], (N : K) ≠ 0 →
      ∀ (Q : W.toAffine.Point), addOrderOf Q = N →
        ∀ (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point),
          φ.ker = AddSubgroup.zmultiples Q →
          (∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
            (φ P).coordsOrZero =
              (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
                  ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
               P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
                  ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) →
          Function.Surjective φ := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ hN Q hQ φ hφker hφ
    have hN0 : N ≠ 0 := by
      rintro rfl
      exact hN (by simp)
    rcases Nat.even_or_odd N with heven | hodd
    · obtain ⟨r, hr⟩ := heven
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact hN0 (by simpa using hr)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr0
      have hN2 : N = 2 * (m + 1) := by omega
      subst hN2
      obtain ⟨h2, hm1, x₀, y₀, h₀, hT, hgy, hΔ₂⟩ := W.exists_two_torsion_data hN Q hQ
      haveI hE₂ : (W.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ₂⟩
      obtain ⟨φ₂, hφ₂⟩ := W.exists_addMonoidHom_coe_eq_veluPointMap2 h2 h₀.1 hgy hΔ₂
      have hQ₂ : addOrderOf (φ₂ Q) = m + 1 := by
        rw [congrFun hφ₂ Q]; exact addOrderOf_veluPointMap2_eq W h2 Q hQ hT hgy hΔ₂
      obtain ⟨ψ, hψker, hψpin⟩ :=
        exists_fullKernelHom_all (m + 1) (W.veluQuotient2 x₀ y₀) hm1 (φ₂ Q) hQ₂
      have hcomp := fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2 W h2 Q hQ hT hgy hΔ₂
      rw [← congrFun hφ₂ Q] at hcomp
      obtain ⟨hχker, hχpin⟩ :=
        W.fullKernelHom_comp_two_pinned h2 Q hQ h₀ hT hgy hΔ₂ φ₂ hφ₂ ψ hψker hψpin hcomp
      have hφχ : φ = (homOfEq hcomp.symm).comp (ψ.comp φ₂) :=
        addMonoidHom_eq_of_ker_eq_of_coordsOrZero_eq Q φ _ hφker hχker
          (fun P hP => by rw [hφ P hP, hχpin P hP])
      have hψsurj : Function.Surjective ψ :=
        ih (m + 1) (by omega) (W.veluQuotient2 x₀ y₀) hm1 (φ₂ Q) hQ₂ ψ hψker hψpin
      have hφ₂surj : Function.Surjective φ₂ := by
        rw [hφ₂]; exact W.veluPointMap2_surjective_of_isAlgClosed h2 h₀.1 hgy hΔ₂
      rw [hφχ]
      exact (homOfEq_surjective hcomp.symm).comp (hψsurj.comp hφ₂surj)
    · haveI : NeZero N := ⟨hN0⟩
      exact fullKernelHom_surjective_of_odd W hN hodd Q hQ φ hφker hφ

private theorem fullKernelHom_surjective_of_isAlgClosed_of_even
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (heven : Even N) (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) :
    Function.Surjective φ := by
  have _ := heven
  exact fullKernelHom_surjective_all N W hN Q hQ φ hφker hφ

end WeierstrassCurve

theorem solution
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (Q : W.toAffine.Point) (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2))) :
    Function.Surjective φ := by
  rcases Nat.even_or_odd N with heven | hodd
  · exact WeierstrassCurve.fullKernelHom_surjective_of_isAlgClosed_of_even W hN heven Q hQ φ hφker hφ
  · exact WeierstrassCurve.fullKernelHom_surjective_of_odd W hN hodd Q hQ φ hφker hφ

end S_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_fullKernelHom_surjective_of_isAlgClosed (solution)
