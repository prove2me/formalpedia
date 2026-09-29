-- Prove2me | solution 1 for WeierstrassCurve.Affine.algHom_eq_of_forall_restrictAlong_placeOfPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/68d36c3c-c257-53ad-8026-e0295bd93343

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import Theorems.Thm_WeierstrassCurve_Affine_algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import Theorems.Thm_P2M_Dup_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal
import Theorems.Thm_P2M_Dup_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal
import Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot
import Theorems.Thm_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

noncomputable section

scoped instance instFactNatPrime2_s13e2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
scoped instance instFactNatPrime3_s13e2 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
scoped instance instFactNatPrime7_s13e2 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation CoordinateRing map Point.some Nonsingular Point.some.inj FunctionField Point CoordinateRing.mk equation_iff_nonsingular equation_iff pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot forall_normFormulaAlong_of_isAlgClosed"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.Polynomial IsDedekindDomain P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.IsDedekindDomain WeierstrassCurve.Affine.CoordinateRing~evalAt P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.AlgebraicCurve"
p2m_open_scoped "Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.Polynomial.Bivariate"

variable {F : Type*} [Field F] {W : Affine F}

theorem S13_ofHeightOneSpectrum_injective {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R W.FunctionField] [IsFractionRing R W.FunctionField] [Algebra F R]
    [IsScalarTower F R W.FunctionField] :
    Function.Injective (AlgebraicCurve.Place.ofHeightOneSpectrum (K := F) (R := R) (F := W.FunctionField)) := by
  intro w₁ w₂ h
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := W.FunctionField) ?_
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact congrArg AlgebraicCurve.Place.toValuationSubring h

namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "XYIdeal quotientXYIdealEquiv YClass mk map XClass isDedekindDomain exists_eq_XYIdeal XYIdeal_isMaximal XYIdeal_ne_bot"
p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt"

theorem algebraMap_eq_mk_C_C (a : F) :
    algebraMap F W.CoordinateRing a = CoordinateRing.mk W (C (C a)) := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  rfl

theorem eq_of_XYIdeal_eq {x₁ y₁ x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (h : XYIdeal W x₁ (C y₁) = XYIdeal W x₂ (C y₂)) : x₁ = x₂ ∧ y₁ = y₂ := by
  have hne : XYIdeal W x₂ (C y₂) ≠ ⊤ := (XYIdeal_isMaximal h₂).ne_top
  have hX₁ : XClass W x₁ ∈ XYIdeal W x₂ (C y₂) :=
    h ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hX₂ : XClass W x₂ ∈ XYIdeal W x₂ (C y₂) := Ideal.subset_span (Set.mem_insert _ _)
  have hY₁ : YClass W (C y₁) ∈ XYIdeal W x₂ (C y₂) :=
    h ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hY₂ : YClass W (C y₂) ∈ XYIdeal W x₂ (C y₂) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  constructor
  · by_contra hx
    apply hne
    have hsub : XClass W x₁ - XClass W x₂ = algebraMap F W.CoordinateRing (x₂ - x₁) := by
      rw [XClass, XClass, ← map_sub, algebraMap_eq_mk_C_C]
      congr 1
      rw [← map_sub]
      congr 1
      rw [map_sub]
      ring
    have hmem := (XYIdeal W x₂ (C y₂)).sub_mem hX₁ hX₂
    rw [hsub] at hmem
    exact Ideal.eq_top_of_isUnit_mem _ hmem
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun hxy => hx hxy.symm)).map
        (algebraMap F W.CoordinateRing))
  · by_contra hy
    apply hne
    have hsub : YClass W (C y₁) - YClass W (C y₂) = algebraMap F W.CoordinateRing (y₂ - y₁) := by
      rw [YClass, YClass, ← map_sub, algebraMap_eq_mk_C_C]
      congr 1
      simp only [map_sub]
      ring
    have hmem := (XYIdeal W x₂ (C y₂)).sub_mem hY₁ hY₂
    rw [hsub] at hmem
    exact Ideal.eq_top_of_isUnit_mem _ hmem
      ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr fun hxy => hy hxy.symm)).map
        (algebraMap F W.CoordinateRing))

def heightOneSpectrumOfEquation {x y : F} (h : W.Equation x y) :
    HeightOneSpectrum W.CoordinateRing where
  asIdeal := XYIdeal W x (C y)
  isPrime := (XYIdeal_isMaximal h).isPrime
  ne_bot := XYIdeal_ne_bot x (C y)

@[scoped simp]
theorem heightOneSpectrumOfEquation_asIdeal {x y : F} (h : W.Equation x y) :
    (heightOneSpectrumOfEquation h).asIdeal = XYIdeal W x (C y) := rfl

theorem exists_sub_algebraMap_mem {x y : F} (h : W.Equation x y) (r : W.CoordinateRing) :
    ∃ c : F, r - algebraMap F W.CoordinateRing c ∈ XYIdeal W x (C y) := by
  set e := quotientXYIdealEquiv (W' := W) (x := x) (y := C y) h
  refine ⟨e (Ideal.Quotient.mk _ r), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  apply e.injective
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes,
    Algebra.algebraMap_self_apply]

end CoordinateRing
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing"

p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing"

def IsFinitePlace (v : AlgebraicCurve.Place F W.FunctionField) : Prop :=
  ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ v.toValuationSubring

def IsFinitePlace.ringHom {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) :
    W.CoordinateRing →+* v.toValuationSubring where
  toFun r := ⟨algebraMap W.CoordinateRing W.FunctionField r, hv r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

@[scoped simp]
theorem IsFinitePlace.coe_ringHom_apply {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) (r : W.CoordinateRing) :
    (hv.ringHom r : W.FunctionField) = algebraMap W.CoordinateRing W.FunctionField r := rfl

p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace"

def IsFinitePlace.centre {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v) :
    Ideal W.CoordinateRing :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).comap hv.ringHom

theorem IsFinitePlace.centre_isPrime {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) : hv.centre.IsPrime :=
  Ideal.IsPrime.comap _

theorem IsFinitePlace.inv_mem {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) {r : W.CoordinateRing} (hr : r ∉ hv.centre) :
    (algebraMap W.CoordinateRing W.FunctionField r)⁻¹ ∈ v.toValuationSubring := by
  have hunit : IsUnit (hv.ringHom r) := by
    rw [IsFinitePlace.centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not] at hr
    exact hr
  obtain ⟨t, ht⟩ := hunit.exists_right_inv
  have ht' : algebraMap W.CoordinateRing W.FunctionField r * (t : W.FunctionField) = 1 := by
    have := congrArg (fun a : v.toValuationSubring => (a : W.FunctionField)) ht
    simpa using this
  rw [inv_eq_of_mul_eq_one_right ht']
  exact t.2

theorem IsFinitePlace.centre_ne_bot {v : AlgebraicCurve.Place F W.FunctionField}
    (hv : IsFinitePlace v) : hv.centre ≠ ⊥ := by
  intro hbot
  apply v.ne_top'
  rw [eq_top_iff]
  rintro z -
  obtain ⟨r, s, hs, hz⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  have hs0 : s ∉ hv.centre := by
    rw [hbot, Ideal.mem_bot]
    exact fun h => nonZeroDivisors.ne_zero hs h
  rw [← hz, div_eq_mul_inv]
  exact mul_mem (hv r) (hv.inv_mem hs0)

variable [IsDedekindDomain W.CoordinateRing]

def placeOfEquation {x y : F} (h : W.Equation x y) :
    AlgebraicCurve.Place F W.FunctionField :=
  AlgebraicCurve.Place.ofHeightOneSpectrum (heightOneSpectrumOfEquation h)

theorem placeOfEquation_injective {x₁ y₁ x₂ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (h : placeOfEquation h₁ = placeOfEquation h₂) :
    x₁ = x₂ ∧ y₁ = y₂ :=
  eq_of_XYIdeal_eq h₂
    (congrArg HeightOneSpectrum.asIdeal (S13_ofHeightOneSpectrum_injective h))

theorem isFinitePlace_placeOfEquation {x y : F} (h : W.Equation x y) :
    IsFinitePlace (placeOfEquation h) := fun r =>
  (heightOneSpectrumOfEquation h).valuation_le_one r

theorem isFinitePlace_iff_exists_placeOfEquation [IsAlgClosed F]
    (v : AlgebraicCurve.Place F W.FunctionField) :
    IsFinitePlace v ↔ ∃ (x y : F) (h : W.Equation x y), v = placeOfEquation h := by
  constructor
  · intro hv

    haveI := hv.centre_isPrime
    have hmax : hv.centre.IsMaximal := Ideal.IsPrime.isMaximal hv.centre_isPrime hv.centre_ne_bot
    obtain ⟨x, y, hxy, hXY⟩ :=
      CoordinateRing.exists_eq_XYIdeal (W := W) (P := hv.centre) hv.centre_ne_bot
    refine ⟨x, y, hxy, ?_⟩

    set w : HeightOneSpectrum W.CoordinateRing := heightOneSpectrumOfEquation hxy with hw
    set A : ValuationSubring W.FunctionField :=
      HeightOneSpectrum.valuationSubringAtPrime W.FunctionField w with hA
    haveI hAded : IsDedekindDomain A := by rw [hA]; infer_instance
    have hle : A ≤ v.toValuationSubring := by
      intro z hz
      rw [hA] at hz
      obtain ⟨r, s, hs, rfl⟩ := hz
      have hs' : s ∉ hv.centre := by
        intro hmem
        rw [hXY] at hmem
        exact hs hmem
      exact mul_mem (hv r) (hv.inv_mem hs')

    have hSP : A.ofPrime (A.idealOfLE v.toValuationSubring hle) = v.toValuationSubring :=
      ValuationSubring.ofPrime_idealOfLE A v.toValuationSubring hle
    rcases eq_or_ne (A.idealOfLE v.toValuationSubring hle) ⊥ with hP | hP
    ·
      exfalso
      apply v.ne_top'
      have h2 : A.ofPrime ⊥ ≤ A.ofPrime (A.idealOfLE v.toValuationSubring hle) :=
        ValuationSubring.ofPrime_le_of_le (h := hP.le)
      rw [ValuationSubring.ofPrime_bot] at h2
      exact top_le_iff.mp (le_trans h2 hSP.le)
    ·
      have hPmax : (A.idealOfLE v.toValuationSubring hle).IsMaximal :=
        Ideal.IsPrime.isMaximal inferInstance hP
      have hPeq : A.idealOfLE v.toValuationSubring hle = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal hPmax
      have h3 : A.ofPrime (A.idealOfLE v.toValuationSubring hle)
          = A.ofPrime (IsLocalRing.maximalIdeal A) :=
        le_antisymm (ValuationSubring.ofPrime_le_of_le (h := hPeq.ge))
          (ValuationSubring.ofPrime_le_of_le (h := hPeq.le))
      rw [ValuationSubring.ofPrime_top] at h3
      have hAv : A = v.toValuationSubring := h3.symm.trans hSP
      refine (AlgebraicCurve.Place.ext ?_).symm
      show (AlgebraicCurve.Place.ofHeightOneSpectrum w).toValuationSubring = v.toValuationSubring
      rw [AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring,
        ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hAv
  · rintro ⟨x, y, h, rfl⟩
    exact isFinitePlace_placeOfEquation h

scoped instance S13_instIsDedekindDomainCoordinateRing [IsAlgClosed F] [W.IsElliptic] :
    IsDedekindDomain W.CoordinateRing :=
  CoordinateRing.isDedekindDomain (W := W)

section CentredGate

variable [DecidableEq F] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

@[scoped simp]
theorem placeOfPoint_some [IsDedekindDomain W.CoordinateRing] {x y : F} (h : W.Nonsingular x y) :
    placeOfPoint (.some x y h) = placeOfEquation h.left :=
  placeOfPoint_some_eq_ofHeightOneSpectrum h (heightOneSpectrumOfEquation h.left) rfl

namespace InfinitePlace

def place : AlgebraicCurve.Place F W.FunctionField := placeOfPoint (0 : W.Point)

theorem deg_eq_one : (place : AlgebraicCurve.Place F W.FunctionField).deg = 1 :=
  deg_placeOfPoint (W := W) 0

theorem not_isFinitePlace [IsAlgClosed F] [W.IsElliptic] :
    ¬ IsFinitePlace (place : AlgebraicCurve.Place F W.FunctionField) := fun h =>
  algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero (W := W) (h _)

theorem eq_of_not_isFinitePlace [IsDedekindDomain W.CoordinateRing]
    (v : AlgebraicCurve.Place F W.FunctionField) (hv : ¬ IsFinitePlace v) :
    v = place := by
  obtain ⟨P, rfl⟩ : ∃ P : W.Point, placeOfPoint P = v :=
    ⟨(pointEquivPlace (W := W)).symm v, (pointEquivPlace (W := W)).apply_symm_apply v⟩
  cases P with
  | zero => rfl
  | some x y h =>
      exact absurd (placeOfPoint_some (W := W) h ▸ isFinitePlace_placeOfEquation h.left) hv

end InfinitePlace
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace"

@[scoped simp]
theorem placeOfPoint_zero : placeOfPoint (.zero : W.Point) = InfinitePlace.place := rfl

theorem placeOfPoint_zero' : placeOfPoint (0 : W.Point) = InfinitePlace.place := rfl

theorem placeOfPoint_injective : Function.Injective (placeOfPoint (W := W)) :=
  (pointEquivPlace (W := W)).injective

theorem placeOfPoint_surjective (_hΔ : W.Δ ≠ 0) : Function.Surjective (placeOfPoint (W := W)) :=
  (pointEquivPlace (W := W)).surjective

theorem placeOfPoint_surjective' : Function.Surjective (placeOfPoint (W := W)) :=
  (pointEquivPlace (W := W)).surjective

end CentredGate
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace"

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation CoordinateRing map Point.some Nonsingular Point.some.inj FunctionField Point CoordinateRing.mk equation_iff_nonsingular equation_iff pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot forall_normFormulaAlong_of_isAlgClosed"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.AlgebraicCurve"

scoped instance instHasPrincipalDivisorsFunctionField_s13 {F : Type*} [Field F]
    {W : Affine F} [W.IsElliptic] : HasPrincipalDivisors F W.FunctionField :=
  WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic W

section AutoNorm
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]

theorem normFormulaAlong_of_elliptic (ι : V.FunctionField →ₐ[F] W.FunctionField)
    (hfin : FiniteAlong F ι) (hsep : SeparableAlong F ι) : NormFormulaAlong F ι hfin :=
  AlgebraicCurve.normFormulaAlong_of_separableAlong ι hfin hsep

end AutoNorm
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section CharFreePMOP

universe u

variable {F : Type u} [Field F] [DecidableEq F]
variable {V W : Affine F}
variable [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

theorem inertiaDegAlong_eq_one_cf (w : AlgebraicCurve.Place F W.FunctionField) :
    w.inertiaDegAlong ι hι = 1 := by
  have h := AlgebraicCurve.Place.deg_restrictAlong_mul_inertiaDegAlong ι hι w
  rw [deg_eq_one (W := V) (w.restrictAlong ι hι), deg_eq_one (W := W) w, one_mul] at h
  exact h

theorem pushforwardAlong_single_eq_cf (w : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    Divisor.pushforwardAlong ι hι (Finsupp.single w n)
      = Finsupp.single (w.restrictAlong ι hι) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one_cf ι hι w, Nat.cast_one, mul_one]

variable (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)

theorem pushforwardAlongDegZero_pointDivisor_cf {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongDegZero ι hι (pointDivisor P) = pointDivisor Q := by
  refine Subtype.ext ?_
  rw [Pic0.coe_pushforwardAlongDegZero, coe_pointDivisor, coe_pointDivisor, map_sub,
    pushforwardAlong_single_eq_cf ι hι, pushforwardAlong_single_eq_cf ι hι, hP, h0]

theorem pushforwardAlongHom_pointClass_cf {P : W.Point} {Q : V.Point}
    (hP : (placeOfPoint P).restrictAlong ι hι = placeOfPoint Q)
    (h0 : (placeOfPoint (0 : W.Point)).restrictAlong ι hι = placeOfPoint (0 : V.Point)) :
    Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P) = pointClass Q := by
  show Pic0.pushforwardAlongHom ι hι hfin hN (Pic0.mk (pointDivisor P))
      = Pic0.mk (pointDivisor Q)
  rw [Pic0.pushforwardAlongHom_mk, pushforwardAlongDegZero_pointDivisor_cf ι hι hP h0]

theorem pointMapOfPushforward_apply_cf (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P
      = genusOnePic0Equiv V (Pic0.pushforwardAlongHom ι hι hfin hN (pointClass P)) := by
  rw [← genusOnePic0Equiv_symm_apply]
  rfl

theorem pointMapOfPushforward_eq_of_seam_cf (g : W.Point → V.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P)) (P : W.Point) :
    pointMapOfPushforward ι hι hfin hN P = g P := by
  rw [pointMapOfPushforward_apply_cf,
    pushforwardAlongHom_pointClass_cf ι hι hfin hN (hg P) ((hg 0).trans (by rw [hg0])),
    genusOnePic0Equiv_apply, pic0ToPoint_pointClass]

end CharFreePMOP
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

namespace IsogenyEndDatum
p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd hfin hι mk ι"
p2m_open "WeierstrassCurve.Affine.IsogenyEndDatum"

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]

private theorem _root_.WeierstrassCurve.Affine.IsogenyEndDatum.normFormulaAlong_auto (D : IsogenyEndDatum W) : NormFormulaAlong F D.ι D.hfin :=
  forall_normFormulaAlong_of_isAlgClosed W D

p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "normFormulaAlong_auto"

private def _root_.WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd' (D : IsogenyEndDatum W) : AddMonoid.End W.Point := D.pointEnd D.normFormulaAlong_auto

p2m_export "WeierstrassCurve.Affine.IsogenyEndDatum" "pointEnd'"
theorem pointEnd_eq_pointEnd' (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) :
    D.pointEnd hN = D.pointEnd' := rfl

theorem pointEnd'_apply (D : IsogenyEndDatum W) (P : W.Point) :
    D.pointEnd' P = genusOnePic0Equiv W
      (Pic0.pushforwardAlongHom D.ι D.hι D.hfin D.normFormulaAlong_auto (pointClass P)) :=
  pointMapOfPushforward_apply_cf D.ι D.hι D.hfin _ P

theorem pointEnd'_eq_of_seam (D : IsogenyEndDatum W) (g : W.Point → W.Point) (hg0 : g 0 = 0)
    (hg : ∀ P, (placeOfPoint P).restrictAlong D.ι D.hι = placeOfPoint (g P)) (P : W.Point) :
    D.pointEnd' P = g P :=
  pointMapOfPushforward_eq_of_seam_cf D.ι D.hι D.hfin _ g hg0 hg P

end IsogenyEndDatum
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk Place.deg_restrictAlong_mul_inertiaDegAlong algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong Divisor.pushforwardAlong Place.ramificationIndexAlong Place.ord_restrictAlong Divisor.pushforwardAlong_single SeparableAlong Place Place.ext Place.coe_algebraMap Place.ord Divisor HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.toValuationSubring Place.ofHeightOneSpectrum_injective normFormulaAlong_of_separableAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg"
end AlgebraicCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace CoordinateRing
end CoordinateRing
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace KwNo3aHbadRiqMorph
end KwNo3aHbadRiqMorph
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace KwNo3aHbadRiqSurjOptionA
end KwNo3aHbadRiqSurjOptionA
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.valuationSubringAtPrime HeightOneSpectrum.asIdeal HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring HeightOneSpectrum.eq_of_valuation_isEquiv_valuation mk HeightOneSpectrum"
p2m_open "IsDedekindDomain"
end IsDedekindDomain
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace IsLocalRing
p2m_export "IsLocalRing" "eq_maximalIdeal ResidueField maximalIdeal mem_maximalIdeal residue_ne_zero_iff_isUnit of_injective ResidueField.algebraMap_eq residue"
p2m_open "IsLocalRing"
end IsLocalRing
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace Polynomial
p2m_export "Polynomial" "C coeff_X X eval_mul support coeff_add coeff algebraMap_eq coeff_eq_zero_of_degree_lt ext_iff degree coeff_sub map algebra coeff_C eval_pow eval_X eval_C nontrivial flt eval_sub mem_support_iff algebraMap_apply coeff_C_mul eval_add ext coeff_X_pow ring not_finite eval"
p2m_open "Polynomial"
end Polynomial
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace Polynomial
p2m_export "Polynomial" "C coeff_X X eval_mul support coeff_add coeff algebraMap_eq coeff_eq_zero_of_degree_lt ext_iff degree coeff_sub map algebra coeff_C eval_pow eval_X eval_C nontrivial flt eval_sub mem_support_iff algebraMap_apply coeff_C_mul eval_add ext coeff_X_pow ring not_finite eval"
namespace Bivariate
p2m_open "Polynomial.Bivariate Polynomial"
end Polynomial.Bivariate
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace RationalIsogenyQuotientSurjectiveUniquenessCurve
end RationalIsogenyQuotientSurjectiveUniquenessCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
p2m_open "WeierstrassCurve"
end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation CoordinateRing map Point.some Nonsingular Point.some.inj FunctionField Point CoordinateRing.mk equation_iff_nonsingular equation_iff pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot forall_normFormulaAlong_of_isAlgClosed"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"
end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation CoordinateRing map Point.some Nonsingular Point.some.inj FunctionField Point CoordinateRing.mk equation_iff_nonsingular equation_iff pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot forall_normFormulaAlong_of_isAlgClosed"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "add some some.inj map_zero map zero mk"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine WeierstrassCurve"
end WeierstrassCurve.Affine.Point
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
namespace WithZero
p2m_export "WithZero" "log_le_log map one le"
p2m_open "WithZero"
end WithZero
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section
section

noncomputable section

p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.Polynomial IsDedekindDomain P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.IsDedekindDomain"

p2m_open_scoped "Polynomial.Bivariate P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.Polynomial.Bivariate"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk Place.deg_restrictAlong_mul_inertiaDegAlong algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong Divisor.pushforwardAlong Place.ramificationIndexAlong Place.ord_restrictAlong Divisor.pushforwardAlong_single SeparableAlong Place Place.ext Place.coe_algebraMap Place.ord Divisor HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.toValuationSubring Place.ofHeightOneSpectrum_injective normFormulaAlong_of_separableAlong"
namespace Place
p2m_export "AlgebraicCurve.Place" "deg_restrictAlong_mul_inertiaDegAlong restrictAlong ramificationIndexAlong inertiaDegAlong ord_restrictAlong ramificationIndex_pos ext coe_algebraMap ResidueField deg adicValuation adicValuation_ne_zero ord ord_zero ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' algebraMap_mem' toValuationSubring mk IsRational evalAt algebraMap_evalAt ofHeightOneSpectrum_injective"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end AlgebraicCurve.Place
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation CoordinateRing map Point.some Nonsingular Point.some.inj FunctionField Point CoordinateRing.mk equation_iff_nonsingular equation_iff pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot forall_normFormulaAlong_of_isAlgClosed"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

p2m_open "WeierstrassCurve.Affine.CoordinateRing~evalAt P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.AlgebraicCurve"

variable {F : Type*} [Field F] {W : Affine F}

variable (v : AlgebraicCurve.Place F W.FunctionField)

theorem exists_equation [IsAlgClosed F] (W : Affine F) (x₀ : F) :
    ∃ y₀ : F, W.Equation x₀ y₀ := by
  set P : F[X] := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X
    - Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hPdef
  have hPdeg : P.degree ≠ 0 := by
    have hcoeff : P.coeff 2 = 1 := by
      rw [hPdef]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
      norm_num
    intro hcon
    have h2 : P.coeff 2 = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt ?_
      rw [hcon]
      norm_num
    rw [hcoeff] at h2
    exact one_ne_zero h2
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root P hPdeg
  refine ⟨y₀, ?_⟩
  rw [equation_iff]
  have h3 : P.eval y₀ = 0 := hy₀
  rw [hPdef] at h3
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h3
  linear_combination h3

end WeierstrassCurve.Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.IsDedekindDomain WithZero P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WithZero IsLocalRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk Place.deg_restrictAlong_mul_inertiaDegAlong algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong Divisor.pushforwardAlong Place.ramificationIndexAlong Place.ord_restrictAlong Divisor.pushforwardAlong_single SeparableAlong Place Place.ext Place.coe_algebraMap Place.ord Divisor HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.toValuationSubring Place.ofHeightOneSpectrum_injective normFormulaAlong_of_separableAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg"

namespace Place
p2m_export "AlgebraicCurve.Place" "deg_restrictAlong_mul_inertiaDegAlong restrictAlong ramificationIndexAlong inertiaDegAlong ord_restrictAlong ramificationIndex_pos ext coe_algebraMap ResidueField deg adicValuation adicValuation_ne_zero ord ord_zero ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' algebraMap_mem' toValuationSubring mk IsRational evalAt algebraMap_evalAt ofHeightOneSpectrum_injective"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg"

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end SinglePlace
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

variable (w : Place K F')

variable [Algebra.IsIntegral F F']

section RestrictDef

variable [Algebra K F] [IsScalarTower K F F']

end RestrictDef
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end Restrict
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end Place
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end AlgebraicCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section
section

p2m_open "Polynomial P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.Polynomial"

universe u r s v

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
p2m_open "WeierstrassCurve"

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : WeierstrassCurve F} [W.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate W] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W] [WeierstrassCurve.Affine.AbelTheorem W] {p : ℕ}

section Preliminaries

variable (W) in
lemma point_infinite : Infinite W.toAffine.Point := by
  refine Infinite.of_injective
    (fun x : F => Affine.Point.some x (WeierstrassCurve.Affine.exists_equation W x).choose
      ((Affine.equation_iff_nonsingular (W := W)).mp (WeierstrassCurve.Affine.exists_equation W x).choose_spec))
    fun x x' hxx' => ?_
  exact (Affine.Point.some.inj hxx').1

end Preliminaries
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section PMulEndo

end PMulEndo
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section Surjectivity

end Surjectivity
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section PowerTorsion

end PowerTorsion
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation CoordinateRing map Point.some Nonsingular Point.some.inj FunctionField Point CoordinateRing.mk equation_iff_nonsingular equation_iff pointMapOfPushforward IsogenyEndDatum IsogenyEndDatum.pointEnd GenusOnePlaceGate pointEquivPlace placeOfPoint deg_eq_one deg_placeOfPoint pointDivisor coe_pointDivisor pointClass AbelTheorem pic0ToPoint_pointClass genusOnePic0Equiv genusOnePic0Equiv_apply genusOnePic0Equiv_symm_apply GenusOnePlaceGate.IsCentred placeOfPoint_some_eq_ofHeightOneSpectrum algebraMap_mk_C_X_notMem_toValuationSubring_placeOfPoint_zero CoordinateRing.isDedekindDomain CoordinateRing.exists_eq_XYIdeal CoordinateRing.XYIdeal_isMaximal CoordinateRing.XYIdeal_ne_bot forall_normFormulaAlong_of_isAlgClosed"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "add some some.inj map_zero map zero mk"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine WeierstrassCurve"

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] [IsAlgClosed K] {W' : Affine R} [Algebra R S] [Algebra R K]
  [Algebra S K] [IsScalarTower R S K] {p : ℕ}

end WeierstrassCurve.Affine.Point
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section
section

noncomputable section

p2m_open "IsLocalRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk Place.deg_restrictAlong_mul_inertiaDegAlong algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong Divisor.pushforwardAlong Place.ramificationIndexAlong Place.ord_restrictAlong Divisor.pushforwardAlong_single SeparableAlong Place Place.ext Place.coe_algebraMap Place.ord Divisor HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.toValuationSubring Place.ofHeightOneSpectrum_injective normFormulaAlong_of_separableAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "deg_restrictAlong_mul_inertiaDegAlong restrictAlong ramificationIndexAlong inertiaDegAlong ord_restrictAlong ramificationIndex_pos ext coe_algebraMap ResidueField deg adicValuation adicValuation_ne_zero ord ord_zero ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' algebraMap_mem' toValuationSubring mk IsRational evalAt algebraMap_evalAt ofHeightOneSpectrum_injective"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.isUnit_mk_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  have huf : (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      = (u : v.toValuationSubring) := Subtype.ext hu
  rw [huf]
  exact u.isUnit

p2m_export "AlgebraicCurve.Place" "isUnit_mk_of_ord_eq_zero"
private theorem _root_.AlgebraicCurve.Place.residue_ne_zero_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    residue v.toValuationSubring (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).mpr (v.isUnit_mk_of_ord_eq_zero hf h)

p2m_export "AlgebraicCurve.Place" "residue_ne_zero_of_ord_eq_zero"
private theorem _root_.AlgebraicCurve.Place.evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f ≠ 0 := by
  intro h0
  have hres := v.algebraMap_evalAt hv (v.mem_of_ord_nonneg hf h.ge)
  rw [h0, _root_.map_zero] at hres
  exact v.residue_ne_zero_of_ord_eq_zero hf h hres.symm

p2m_export "AlgebraicCurve.Place" "evalAt_ne_zero"
end Place
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "pushforwardAlong pushforwardAlong_single degree"
p2m_open "AlgebraicCurve.Divisor"

end Divisor
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

namespace WeilDatum

end WeilDatum
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end AlgebraicCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"
end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section
section

noncomputable section

p2m_open "IsLocalRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk Place.deg_restrictAlong_mul_inertiaDegAlong algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong Divisor.pushforwardAlong Place.ramificationIndexAlong Place.ord_restrictAlong Divisor.pushforwardAlong_single SeparableAlong Place Place.ext Place.coe_algebraMap Place.ord Divisor HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.toValuationSubring Place.ofHeightOneSpectrum_injective normFormulaAlong_of_separableAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg"

namespace Place
p2m_export "AlgebraicCurve.Place" "deg_restrictAlong_mul_inertiaDegAlong restrictAlong ramificationIndexAlong inertiaDegAlong ord_restrictAlong ramificationIndex_pos ext coe_algebraMap ResidueField deg adicValuation adicValuation_ne_zero ord ord_zero ord_unit_smul_zpow exists_unit_mul_zpow ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring ne_top' algebraMap_mem' toValuationSubring mk IsRational evalAt algebraMap_evalAt ofHeightOneSpectrum_injective"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_sub_evalAt_pos (hrat : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring :=
    sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  ·
    exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField
        (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (v.evalAt f)
          = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := v.ord_nonneg_of_mem hmem
    omega

p2m_export "AlgebraicCurve.Place" "ord_sub_evalAt_pos"
variable [HasPrincipalDivisors K F]

end Place
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end AlgebraicCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

namespace ModularCurve

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.AlgebraicCurve"

variable (N : ℕ) [NeZero N]

end ModularCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Pic0.pushforwardAlongDegZero Pic0.coe_pushforwardAlongDegZero Pic0.pushforwardAlongHom Pic0.pushforwardAlongHom_mk Place.deg_restrictAlong_mul_inertiaDegAlong algebraAlong isScalarTower_along isIntegral_along FiniteAlong NormFormulaAlong Divisor.pushforwardAlong Place.ramificationIndexAlong Place.ord_restrictAlong Divisor.pushforwardAlong_single SeparableAlong Place Place.ext Place.coe_algebraMap Place.ord Divisor HasPrincipalDivisors Pic0 Pic0.mk Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor Place.toValuationSubring Place.ofHeightOneSpectrum_injective normFormulaAlong_of_separableAlong"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg"

theorem finite_setOf_ord_ne_zero_of_finiteDimensional {K : Type*} [Field K] {F' : Type*} [Field F']
    [Algebra K F'] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) :
    {w : Place K F' | w.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F') f hf
  refine (D.support.finite_toSet).subset ?_
  intro w hw
  have hw' : D w ≠ 0 := by rw [hD w]; exact hw
  exact Finsupp.mem_support_iff.mpr hw'

end AlgebraicCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section
section

set_option maxHeartbeats 3200000

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.Point"
p2m_open_scoped "WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine a₃ a₁ map mk a₄ Jacobian a₂ a₆ Affine.Point.some Affine.Point.some.inj IsIntegral toAffine Affine.Point Affine.equation_iff_nonsingular Δ Affine.GenusOnePlaceGate Affine.AbelTheorem Affine.GenusOnePlaceGate.IsCentred hasPrincipalDivisors_functionField_of_isElliptic Affine.forall_normFormulaAlong_of_isAlgClosed"
p2m_open "WeierstrassCurve"

namespace KwNo3aHbadRiqsucrA1a

open KwNo3aHbadRiqMorph KwNo3aHbadRiqSurjOptionA
open RationalIsogenyQuotientSurjectiveUniquenessCurve
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.AlgebraicCurve"

section RouteEta

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem no3ahbad_riqsucr_a1a_ord_pos_of_restrictAlong_ord_pos
    (φ : F' →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (v : Place K F)
    (f : F') (c : K) (hord : (v.restrictAlong φ hφ).ord (f - algebraMap K F' c) > 0) :
    v.ord (φ f - algebraMap K F c) > 0 := by
  have hrw : φ f - algebraMap K F c = φ (f - algebraMap K F' c) := by
    rw [map_sub, AlgHom.commutes]
  rw [hrw, Place.ord_restrictAlong φ hφ v (f - algebraMap K F' c)]
  refine mul_pos ?_ hord
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact_mod_cast v.ramificationIndex_pos (F := F')

end RouteEta
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section FiniteZeros

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {V : Affine F} [IsDedekindDomain V.CoordinateRing] [HasPrincipalDivisors F V.FunctionField] [WeierstrassCurve.Affine.GenusOnePlaceGate V] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred V] [WeierstrassCurve.Affine.AbelTheorem V]

theorem no3ahbad_riqsucr_a1a_finite_ord_ne_zero (h : V.FunctionField) (hne : h ≠ 0) :
    {P : V.Point | (placeOfPoint P).ord h ≠ 0}.Finite := by
  have hfin : {v : Place F V.FunctionField | v.ord h ≠ 0}.Finite :=
    finite_setOf_ord_ne_zero_of_finiteDimensional hne
  refine Set.Finite.of_finite_image (f := placeOfPoint)
    (hfin.subset ?_) (Set.injOn_of_injective placeOfPoint_injective)
  rintro v ⟨P, hP, rfl⟩; exact hP

end FiniteZeros
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

section Ext

variable {K F' : Type*} [Field K] [IsAlgClosed K] [Field F'] [Algebra K F']
variable {V : Affine K} [DecidableEq K] [IsDedekindDomain V.CoordinateRing] [HasPrincipalDivisors K V.FunctionField] [WeierstrassCurve.Affine.GenusOnePlaceGate V] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred V] [WeierstrassCurve.Affine.AbelTheorem V]

theorem no3ahbad_riqsucr_a1a_exists_residue (w : Place K F')
    (hsurj : Function.Surjective (algebraMap K w.ResidueField))
    (f : F') (hf : w.ord f ≥ 0) :
    ∃ c : K, f = algebraMap K F' c ∨ w.ord (f - algebraMap K F' c) > 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, Or.inl (algebraMap K F').map_zero.symm⟩
  refine ⟨w.evalAt f, ?_⟩
  rcases eq_or_ne (f - algebraMap K F' (w.evalAt f)) 0 with heq | hne
  · exact Or.inl (sub_eq_zero.mp heq)
  · exact Or.inr (w.ord_sub_evalAt_pos hsurj (w.mem_of_ord_nonneg hf0 hf) hne)

theorem no3ahbad_riqsucr_a1a_ord_sub_pos_of_pos {L : Type*} [Field L] [Algebra K L]
    (v : Place K L) {a b : L} (ha : v.ord a > 0) (hb : v.ord b > 0) (hab : a ≠ b) :
    v.ord (a - b) > 0 := by
  have ha0 : a ≠ 0 := fun h => absurd (h ▸ ha) (by simp [v.ord_zero])
  have hb0 : b ≠ 0 := fun h => absurd (h ▸ hb) (by simp [v.ord_zero])
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hval : v.adicValuation (a - b) ≤ max (v.adicValuation a) (v.adicValuation b) := by
    have h := v.adicValuation.map_add a (-b)
    rwa [← sub_eq_add_neg, Valuation.map_neg] at h
  rcases max_cases (v.adicValuation a) (v.adicValuation b) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
    rw [hmax] at hval
  · have := (WithZero.log_le_log (v.adicValuation_ne_zero hne)
      (v.adicValuation_ne_zero ha0)).mpr hval
    simp only [Place.ord] at ha ⊢; omega
  · have := (WithZero.log_le_log (v.adicValuation_ne_zero hne)
      (v.adicValuation_ne_zero hb0)).mpr hval
    simp only [Place.ord] at hb ⊢; omega

theorem no3ahbad_riqsucr_a1a_algHom_ext_of_restrictAlong_placeOfPoint_eq
    (hVinf : Infinite V.Point) (hrat : ∀ w : Place K F', w.IsRational)
    (φ₁ φ₂ : F' →ₐ[K] V.FunctionField)
    (hφ₁ : φ₁.toRingHom.IsIntegral) (hφ₂ : φ₂.toRingHom.IsIntegral)
    (hres : ∀ P : V.Point,
      (placeOfPoint P).restrictAlong φ₁ hφ₁ = (placeOfPoint P).restrictAlong φ₂ hφ₂) :
    φ₁ = φ₂ := by
  ext f
  by_contra hne
  have hne' : φ₁ f - φ₂ f ≠ 0 := sub_ne_zero.mpr hne
  have hfin := no3ahbad_riqsucr_a1a_finite_ord_ne_zero (V := V) (φ₁ f - φ₂ f) hne'
  have hpoles : {P : V.Point |
      ((placeOfPoint P).restrictAlong φ₁ hφ₁).ord f < 0}.Finite := by
    rcases eq_or_ne (φ₁ f) 0 with h0 | h0
    ·
      exact absurd (by
        have hf0 : f = 0 := φ₁.injective (by simp [h0])
        simp [hf0]) hne'
    · refine (no3ahbad_riqsucr_a1a_finite_ord_ne_zero (V := V) (φ₁ f) h0).subset ?_
      intro P hP
      simp only [Set.mem_setOf_eq] at hP ⊢
      rw [Place.ord_restrictAlong φ₁ hφ₁ (placeOfPoint P) f]
      exact ne_of_lt (mul_neg_of_pos_of_neg (by
        unfold Place.ramificationIndexAlong
        letI := algebraAlong φ₁; haveI := isScalarTower_along φ₁
        haveI := isIntegral_along φ₁ hφ₁
        exact_mod_cast (placeOfPoint P).ramificationIndex_pos (F := F')) hP)
  have hcofin : {P : V.Point | (placeOfPoint P).ord (φ₁ f - φ₂ f) > 0}ᶜ ⊆
      {P | ((placeOfPoint P).restrictAlong φ₁ hφ₁).ord f < 0} := by
    intro P hP
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hP ⊢
    by_contra hge
    simp only [not_lt] at hge
    obtain ⟨c, hc⟩ := no3ahbad_riqsucr_a1a_exists_residue
      ((placeOfPoint P).restrictAlong φ₁ hφ₁) (hrat _) f hge
    rcases hc with heq | hc
    ·
      exact absurd (heq ▸ (φ₁.commutes c).trans (φ₂.commutes c).symm) hne
    have h1 := no3ahbad_riqsucr_a1a_ord_pos_of_restrictAlong_ord_pos φ₁ hφ₁
      (placeOfPoint P) f c hc
    have h2 := no3ahbad_riqsucr_a1a_ord_pos_of_restrictAlong_ord_pos φ₂ hφ₂
      (placeOfPoint P) f c (hres P ▸ hc)
    have h12 := no3ahbad_riqsucr_a1a_ord_sub_pos_of_pos (placeOfPoint P) h1 h2
      (fun heq => hne (sub_left_inj.mp heq))
    simp only [sub_sub_sub_cancel_right] at h12
    exact absurd h12 (not_lt.mpr hP)
  have hcof_fin : {P : V.Point | (placeOfPoint P).ord (φ₁ f - φ₂ f) > 0}ᶜ.Finite :=
    hpoles.subset hcofin
  have hset_fin : (Set.univ : Set V.Point).Finite := by
    rw [← Set.compl_union_self {P | (placeOfPoint P).ord (φ₁ f - φ₂ f) > 0}]
    exact hcof_fin.union (hfin.subset (fun P hP => ne_of_gt hP))
  exact hVinf.not_finite (Set.finite_univ_iff.mp hset_fin)

end Ext
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end KwNo3aHbadRiqsucrA1a
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine.IsFinitePlace P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine"

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg" in open _root_.WeierstrassCurve _root_.P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve _root_.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq.AlgebraicCurve in
universe u in
theorem solution
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K]
    {V : WeierstrassCurve.Affine K} [V.IsElliptic]
    [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]
    {F' : Type*} [Field F'] [Algebra K F'] (hrat : ∀ w : AlgebraicCurve.Place K F', w.IsRational)
    (φ₁ φ₂ : F' →ₐ[K] V.FunctionField)
    (hφ₁ : φ₁.toRingHom.IsIntegral) (hφ₂ : φ₂.toRingHom.IsIntegral)
    (hres : ∀ P : V.Point,
      (placeOfPoint P).restrictAlong φ₁ hφ₁ = (placeOfPoint P).restrictAlong φ₂ hφ₂) :
    φ₁ = φ₂ :=
  WeierstrassCurve.KwNo3aHbadRiqsucrA1a.no3ahbad_riqsucr_a1a_algHom_ext_of_restrictAlong_placeOfPoint_eq
    (WeierstrassCurve.point_infinite (W := V)) hrat φ₁ φ₂ hφ₁ hφ₂ hres

end
end S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_algHom_eq_of_forall_restrictAlong_placeOfPoint_eq (solution)
