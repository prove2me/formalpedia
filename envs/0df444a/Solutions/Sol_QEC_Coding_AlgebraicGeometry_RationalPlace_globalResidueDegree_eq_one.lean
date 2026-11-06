-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalPlace.globalResidueDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:20:25.283968+00:00
-- url     : https://prove2.me/submissions/f1489969-b93b-424b-9a42-3af36cc2175a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residueAlgebra_algebraMap
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_affine
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_inverseFibre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


section
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry
private theorem rationalPlaceDegree_rankOneDiscrete_of_surjective
    {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : v.IsRankOneDiscrete := by
  let γ : ℤᵐ⁰ˣ := Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp)
  refine ⟨γ, ?_, ?_⟩
  · apply Subgroup.ext
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hv x.1
      have ha0 : v a ≠ 0 := by simpa only [ha] using x.ne_zero
      have hunit : Units.mk0 (v a) ha0 = x := Units.ext ha
      rw [← hunit]
      exact MonoidWithZeroHom.mem_valueGroup (MonoidWithZeroHom.ofClass v)
        (show (Units.mk0 (v a) ha0 : ℤᵐ⁰ˣ).1 ∈ Set.range v from ⟨a, rfl⟩)
    · intro hx
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨-WithZero.log x.1, ?_⟩
      apply Units.ext
      rw [Units.val_zpow_eq_zpow_val]
      change (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ (-WithZero.log x.1) = x.1
      rw [← WithZero.exp_zsmul]
      simpa only [Int.zsmul_eq_mul, neg_mul_neg, one_mul, mul_one] using
        (WithZero.exp_log x.ne_zero)
  · change (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1
    simpa using (WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by decide))
private theorem rationalPlaceDegree_normalizedCodomainOrderAuto_eq_id
    (φ : ℤᵐ⁰ ≃*o ℤᵐ⁰) : φ = OrderMonoidIso.refl ℤᵐ⁰ := by
  have hunit : rationalPlaceDegree_normalizedUnitOrderAuto φ = OrderMonoidIso.refl (Multiplicative ℤ) :=
    Subsingleton.elim _ _
  calc
    φ = OrderMonoidIso.withZero (rationalPlaceDegree_normalizedUnitOrderAuto φ) :=
      (OrderMonoidIso.withZero.apply_symm_apply φ).symm
    _ = OrderMonoidIso.withZero (OrderMonoidIso.refl (Multiplicative ℤ)) :=
      congrArg OrderMonoidIso.withZero hunit
    _ = OrderMonoidIso.refl ℤᵐ⁰ := by
      apply OrderMonoidIso.toMulEquiv_injective
      apply MulEquiv.ext
      intro x
      cases x <;> rfl
private theorem rationalPlaceDegree_normalizedCodomainOrderAuto_apply_restrict
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (h : v.IsEquiv w) (a : F) :
    rationalPlaceDegree_normalizedCodomainOrderAuto v w h
        (rationalPlaceDegree_normalizedValueGroupOrderIso v (v.restrict a)) =
      rationalPlaceDegree_normalizedValueGroupOrderIso w (w.restrict a) := by
  change rationalPlaceDegree_normalizedValueGroupOrderIso w
      (h.orderMonoidIso
        ((rationalPlaceDegree_normalizedValueGroupOrderIso v).symm
          (rationalPlaceDegree_normalizedValueGroupOrderIso v (v.restrict a)))) =
    rationalPlaceDegree_normalizedValueGroupOrderIso w (w.restrict a)
  rw [(rationalPlaceDegree_normalizedValueGroupOrderIso v).symm_apply_apply]
  rw [h.orderMonoidIso_spec]
private theorem rationalPlaceDegree_normalizedCodomainOrderAuto_value_eq
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    [v.IsRankOneDiscrete] [w.IsRankOneDiscrete]
    (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (h : v.IsEquiv w)
    (hφ : rationalPlaceDegree_normalizedCodomainOrderAuto v w h = OrderMonoidIso.refl ℤᵐ⁰)
    (a : F) : v a = w a := by
  calc
    v a = rationalPlaceDegree_normalizedValueGroupOrderIso v (v.restrict a) :=
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (v := v) hv a).symm
    _ = rationalPlaceDegree_normalizedCodomainOrderAuto v w h
          (rationalPlaceDegree_normalizedValueGroupOrderIso v (v.restrict a)) := by
      rw [hφ]
      rfl
    _ = rationalPlaceDegree_normalizedValueGroupOrderIso w (w.restrict a) :=
      rationalPlaceDegree_normalizedCodomainOrderAuto_apply_restrict v w h a
    _ = w a :=
      Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (v := w) hw a
private theorem rationalPlaceDegree_valuation_eq_of_surjective_isEquiv_withZeroMulInt
    {F : Type*} [Field F]
    (v w : Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (h : v.IsEquiv w) : v = w := by
  letI : v.IsRankOneDiscrete := rationalPlaceDegree_rankOneDiscrete_of_surjective v hv
  letI : w.IsRankOneDiscrete := rationalPlaceDegree_rankOneDiscrete_of_surjective w hw
  let φ := rationalPlaceDegree_normalizedCodomainOrderAuto v w h
  have hφ : φ = OrderMonoidIso.refl ℤᵐ⁰ := rationalPlaceDegree_normalizedCodomainOrderAuto_eq_id φ
  apply Valuation.ext
  intro a
  exact rationalPlaceDegree_normalizedCodomainOrderAuto_value_eq v w hv hw h hφ a
private theorem rationalPlaceDegree_regularCentreLocalizationToValuationRing_comp
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (rationalPlaceDegree_regularCentreLocalizationToValuationRing P ht).comp
      (algebraMap (FunctionField.ringOfIntegers k F)
        (rationalPlaceDegree_regularCentreCanonicalLocalization P ht)) =
      rationalPlaceDegree_ringOfIntegersToValuationRing (v := P.valuation) ht := by
  simpa [rationalPlaceDegree_regularCentreLocalizationToValuationRing] using
    (IsLocalization.lift_comp (rationalPlaceDegree_regularCentre_primeCompl_maps_to_unit P ht))
private theorem rationalPlaceDegree_regularCentreLocalization_coe_triangle
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    (ValuationSubring.subtype P.valuation.valuationSubring).comp
      (rationalPlaceDegree_regularCentreLocalizationToValuationRing P ht) =
      ValuationSubring.subtype (rationalPlaceDegree_regularCentreCanonicalLocalization P ht) := by
  apply IsLocalization.ringHom_ext
    (rationalPlaceDegree_regularCentreHeightOne P ht).asIdeal.primeCompl
  ext b
  change ((rationalPlaceDegree_regularCentreLocalizationToValuationRing P ht
      (algebraMap (FunctionField.ringOfIntegers k F)
        (rationalPlaceDegree_regularCentreCanonicalLocalization P ht) b) :
        P.valuation.valuationSubring) : F) = algebraMap
      (FunctionField.ringOfIntegers k F) F b
  rw [← RingHom.comp_apply, rationalPlaceDegree_regularCentreLocalizationToValuationRing_comp]
  rfl
private theorem rationalPlaceDegree_regularCentreCanonicalLocalization_le_placeValuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    rationalPlaceDegree_regularCentreCanonicalLocalization P ht ≤ P.valuation.valuationSubring := by
  intro x hx
  let xC : rationalPlaceDegree_regularCentreCanonicalLocalization P ht := ⟨x, hx⟩
  have htriangle := RingHom.congr_fun
    (rationalPlaceDegree_regularCentreLocalization_coe_triangle P ht) xC
  have hxF :
      ((rationalPlaceDegree_regularCentreLocalizationToValuationRing P ht xC :
        P.valuation.valuationSubring) : F) = x := by
    simpa only [RingHom.comp_apply, ValuationSubring.coe_subtype] using htriangle
  rw [← hxF]
  exact (rationalPlaceDegree_regularCentreLocalizationToValuationRing P ht xC).property
private theorem rationalPlaceDegree_globalPlace_valuation_isNontrivial
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : GlobalPlace k F) : P.valuation.IsNontrivial := by
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨P.uniformizer, ?_, ?_⟩
  · apply P.valuation.ne_zero_iff.mp
    rw [P.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [P.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
private theorem rationalPlaceDegree_globalPlace_valuationSubring_ne_top
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    (P : GlobalPlace k F) : P.valuation.valuationSubring ≠ ⊤ := by
  intro htop
  exact ((Valuation.valuationSubring_eq_top_iff (v := P.valuation)).mp htop)
    (rationalPlaceDegree_globalPlace_valuation_isNontrivial P)
private theorem rationalPlaceDegree_regularCentreCanonicalLocalization_eq_placeValuationSubring
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    rationalPlaceDegree_regularCentreCanonicalLocalization P ht = P.valuation.valuationSubring :=
  ValuationSubring.eq_of_le_of_ne_top _
    (rationalPlaceDegree_regularCentreCanonicalLocalization_le_placeValuationSubring P ht)
    (rationalPlaceDegree_globalPlace_valuationSubring_ne_top P)
private theorem rationalPlaceDegree_placeValuation_isEquiv_regularCentreAdicValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    P.valuation.IsEquiv ((rationalPlaceDegree_regularCentreHeightOne P ht).valuation F) := by
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact (rationalPlaceDegree_regularCentreCanonicalLocalization_eq_placeValuationSubring P ht).symm.trans
    ((rationalPlaceDegree_regularCentreHeightOne P ht).valuationSubringAtPrime_eq_valuationSubring)
private theorem rationalPlaceDegree_placeValuation_eq_regularCentreAdicValuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [Algebra k F] [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (P : GlobalPlace k F)
    (ht : P.valuation (((algebraMap (FunctionField.ringOfIntegers k F) F).comp
      (algebraMap k[X] (FunctionField.ringOfIntegers k F))) Polynomial.X) ≤ 1) :
    P.valuation = (rationalPlaceDegree_regularCentreHeightOne P ht).valuation F := by
  exact rationalPlaceDegree_valuation_eq_of_surjective_isEquiv_withZeroMulInt
    P.valuation
    ((rationalPlaceDegree_regularCentreHeightOne P ht).valuation F)
    P.normalized
    ((rationalPlaceDegree_regularCentreHeightOne P ht).valuation_surjective F)
    (rationalPlaceDegree_placeValuation_isEquiv_regularCentreAdicValuation P ht)
private theorem rationalPlaceDegree_affineResidueDegree_eq_one_of_rationalGlobal
    {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
    [Algebra k[X] F] [Algebra k⟮X⟯ F]
    [IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F]
    (Q : RationalPlace k F) (C : AffinePlace.carrier k F)
    (hvaluation : Q.place.valuation = C.valuation F) :
    AffinePlace.residueDegree k F C = 1 := by
  classical
  let e := rationalPlaceDegree_affineResidueFieldEquiv Q.place C hvaluation
  unfold AffinePlace.residueDegree
  letI : Algebra k (AffinePlace.residueField k F C) := AffinePlace.residueAlgebra k F C
  letI : FiniteDimensional k (AffinePlace.residueField k F C) :=
    AffinePlace.residueField_finiteDimensional k F C
  apply Module.finrank_of_bijective_algebraMap
  rw [AffinePlace.residueAlgebra_algebraMap]
  letI : Fintype k := Fintype.ofFinite k
  letI : Finite (GlobalPlace.residueField Q.place) :=
    Finite.of_equiv k Q.constantsEquiv.toEquiv
  letI : Fintype (GlobalPlace.residueField Q.place) := Fintype.ofFinite _
  letI : Finite (AffinePlace.residueField k F C) :=
    Finite.of_equiv (GlobalPlace.residueField Q.place) e.toEquiv.symm
  letI : Fintype (AffinePlace.residueField k F C) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card
    (AffinePlace.constantsToResidue k F C)).mpr
  refine ⟨(AffinePlace.constantsToResidue k F C).injective, ?_⟩
  calc
      Fintype.card k = Fintype.card (GlobalPlace.residueField Q.place) :=
        Fintype.card_congr Q.constantsEquiv.toEquiv
      _ = Fintype.card (AffinePlace.residueField k F C) :=
        Fintype.card_congr e.toEquiv.symm
private theorem rationalPlaceDegree_original_coordinate_dichotomy
    {k F : Type*} [Field k] [Finite k] [Field F]
    [ρ : Algebra k⟮X⟯ F] [κ : Algebra k F]
    (P : @GlobalPlace k F _ _ _ κ) :
    P.valuation (rationalPlaceDegree_originalCoordinate ρ) ≤ 1 ∨
      P.valuation (rationalPlaceDegree_originalInverseCoordinate ρ) < 1 := by
  by_cases h : P.valuation (rationalPlaceDegree_originalCoordinate ρ) ≤ 1
  · exact Or.inl h
  · right
    rw [rationalPlaceDegree_originalInverseCoordinate, P.valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ (lt_of_not_ge h)
private theorem rationalPlaceDegree_directIntegralCoordinate_eq_originalCoordinate
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [_root_.FunctionField k F]
    [Algebra.IsSeparable k⟮X⟯ F] :
    algebraMap (_root_.FunctionField.ringOfIntegers k F) F
      (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X) =
        rationalPlaceDegree_originalCoordinate ρ := by
  change ((algebraMap (_root_.FunctionField.ringOfIntegers k F) F).comp
    (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F))) Polynomial.X =
      ρ.algebraMap RatFunc.X
  calc
    _ = (algebraMap k[X] F) Polynomial.X := by
      rw [← IsScalarTower.algebraMap_eq k[X]
        (_root_.FunctionField.ringOfIntegers k F) F]
    _ = ρ.algebraMap ((algebraMap k[X] k⟮X⟯) Polynomial.X) := by
      rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F]
    _ = ρ.algebraMap RatFunc.X := rfl
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
namespace RationalPlace
theorem _root_.solution
    {k F : Type*} [Field k] [Finite k] [Field F] [κ : Algebra k F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (Q : RationalPlace k F) :
    GlobalPlace.residueDegree Q.place = 1 := by
  rcases rationalPlaceDegree_original_coordinate_dichotomy Q.place with hdirect | hinverse
  · let hbound : Q.place.valuation
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
          (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 := by
      rw [rationalPlaceDegree_directIntegralCoordinate_eq_originalCoordinate]
      exact hdirect
    let C := rationalPlaceDegree_regularCentreHeightOne Q.place hbound
    have hvaluation : Q.place.valuation = C.valuation F :=
      rationalPlaceDegree_placeValuation_eq_regularCentreAdicValuation Q.place hbound
    rw [GlobalPlace.residueDegree_eq_affine Q.place C hvaluation]
    exact rationalPlaceDegree_affineResidueDegree_eq_one_of_rationalGlobal Q C hvaluation
  · letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
      (oldRationalAlgebra := ρ) k F
    letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
      (oldRationalAlgebra := ρ) k F
    letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
      (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
    letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
      (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
    let hbound : Q.place.valuation
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
          (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) ≤ 1 :=
      le_of_lt (by
        rw [rationalPlaceDegree_inverseIntegralCoordinate_eq_originalInverseCoordinate
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
        exact hinverse)
    let D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F :=
      rationalPlaceDegree_inverseCentreInInfinityFibre (π := π) (ρ := ρ) (τ := τ) (φ := φ)
        (σ := σ) Q.place hinverse
    have hvaluation : Q.place.valuation = D.1.valuation F := by
      change Q.place.valuation = (rationalPlaceDegree_regularCentreHeightOne Q.place hbound).valuation F
      exact rationalPlaceDegree_placeValuation_eq_regularCentreAdicValuation Q.place hbound
    rw [GlobalPlace.residueDegree_eq_inverseFibre
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) Q.place D (by
      change Q.place.valuation = D.1.valuation F
      exact hvaluation)]
    change AffinePlace.residueDegree k F D.1 = 1
    exact rationalPlaceDegree_affineResidueDegree_eq_one_of_rationalGlobal Q D.1 hvaluation
end RationalPlace
end QEC.Coding.AlgebraicGeometry
