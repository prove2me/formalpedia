-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:17:51.347366+00:00
-- url     : https://prove2.me/submissions/17ffbd5b-a0d0-4df5-a4ae-47678f12191c

import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing


section
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry
private theorem inverseFibreGlobalPlaceAt_valuation
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (κ : Algebra k F)
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D) =
      inverseFibreRawValuation D := rfl
private theorem order_eq_of_rawValuation_eq
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    {κ₁ κ₂ : Algebra k F}
    (P : @GlobalPlace k F _ _ _ κ₁) (Q : @GlobalPlace k F _ _ _ κ₂)
    (hvaluation : @GlobalPlace.valuation k F _ _ _ κ₁ P =
      @GlobalPlace.valuation k F _ _ _ κ₂ Q) (f : F) :
    @GlobalPlace.order k F _ _ _ κ₁ P f =
      @GlobalPlace.order k F _ _ _ κ₂ Q f := by
  change -WithZero.log (@GlobalPlace.valuation k F _ _ _ κ₁ P f) =
    -WithZero.log (@GlobalPlace.valuation k F _ _ _ κ₂ Q f)
  rw [hvaluation]
private theorem inverseFibrePrincipalDivisor_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    inverseFibrePrincipalDivisor (k := k) (F := F) f D =
      -WithZero.log (inverseFibreRawValuation
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) D (f : F)) := by
  unfold inverseFibrePrincipalDivisor
  letI : Algebra k⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : Algebra k[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := ρ) k F
  letI : IsScalarTower k[X] k⟮X⟯ F := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := ρ) k F
  letI : _root_.FunctionField k F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := ρ) (oldFunctionField := φ) k F
  letI : Algebra.IsSeparable k⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := ρ) (oldSeparable := σ) k F
  letI : Fintype (InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :=
    InverseAffinePlace.infinityFibreFintype (oldRationalAlgebra := ρ) k F
  simpa only [Finsupp.onFinset_apply]
private theorem mapDomain_inl_apply
    {α β M : Type*} [AddCommMonoid M] (u : α →₀ M) (a : α) :
    Finsupp.mapDomain Sum.inl u (Sum.inl a : Sum α β) = u a :=
  Finsupp.mapDomain_apply Sum.inl_injective u a
private theorem mapDomain_inr_apply
    {α β M : Type*} [AddCommMonoid M] (v : β →₀ M) (b : β) :
    Finsupp.mapDomain Sum.inr v (Sum.inr b : Sum α β) = v b :=
  Finsupp.mapDomain_apply Sum.inr_injective v b
private theorem mapDomain_inr_at_inl
    {α β M : Type*} [AddCommMonoid M] (v : β →₀ M) (a : α) :
    Finsupp.mapDomain Sum.inr v (Sum.inl a : Sum α β) = 0 := by
  apply Finsupp.mapDomain_notin_range
  intro h
  rcases h with ⟨b, h⟩
  cases h
private theorem mapDomain_inl_at_inr
    {α β M : Type*} [AddCommMonoid M] (u : α →₀ M) (b : β) :
    Finsupp.mapDomain Sum.inl u (Sum.inr b : Sum α β) = 0 := by
  apply Finsupp.mapDomain_notin_range
  intro h
  rcases h with ⟨a, h⟩
  cases h
private theorem correctedTwoChartToGlobalPlace_inl_raw
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : AffinePlace.carrier k F) :
    (correctedTwoChartToGlobalPlace (Sum.inl C : CorrectedTwoChartPlace k F)).valuation =
      (repackageRawGlobalPlace κ (AffinePlace.globalPlace k F C)).valuation := rfl
private theorem correctedTwoChartToGlobalPlace_inr_raw
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F) :
    (correctedTwoChartToGlobalPlace (Sum.inr D : CorrectedTwoChartPlace k F)).valuation =
      @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D) := by
  change inverseFibreRawValuation D =
    @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D)
  rw [inverseFibreGlobalPlaceAt_valuation]
private theorem twoChartPrincipalDivisor_apply
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) (C : CorrectedTwoChartPlace k F) :
    twoChartPrincipalDivisor (k := k) (F := F) f C =
      GlobalPlace.order (correctedTwoChartToGlobalPlace C) (f : F) := by
  cases C with
  | inl C =>
      change Finsupp.mapDomain Sum.inl (AffinePlace.affinePrincipalDivisor k F f)
          (Sum.inl C) +
          Finsupp.mapDomain Sum.inr (inverseFibrePrincipalDivisor (k := k) (F := F) f)
            (Sum.inl C) = _
      rw [mapDomain_inl_apply, mapDomain_inr_at_inl, add_zero,
        AffinePlace.affinePrincipalDivisor_apply]
      exact order_eq_of_rawValuation_eq _ _
        (correctedTwoChartToGlobalPlace_inl_raw (k := k) (F := F) C).symm (f : F)
  | inr D =>
      change Finsupp.mapDomain Sum.inl (AffinePlace.affinePrincipalDivisor k F f)
          (Sum.inr D) +
          Finsupp.mapDomain Sum.inr (inverseFibrePrincipalDivisor (k := k) (F := F) f)
            (Sum.inr D) = _
      rw [mapDomain_inl_at_inr, zero_add, mapDomain_inr_apply,
        inverseFibrePrincipalDivisor_apply]
      exact order_eq_of_rawValuation_eq _ _
        (correctedTwoChartToGlobalPlace_inr_raw (k := k) (F := F) D).symm (f : F)
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) (P : @GlobalPlace k F _ _ _ κ) :
    GlobalPlace.principalDivisor (k := k) (F := F) f P = GlobalPlace.order P (f : F) := by
  rw [GlobalPlace.principalDivisor, Finsupp.equivMapDomain_apply]
  have hpoint := twoChartPrincipalDivisor_apply (k := k) (F := F) f
    ((chartGlobalPlaceEquiv (k := k) (F := F)).symm P)
  rw [← chartGlobalPlaceEquiv_apply] at hpoint
  simpa using hpoint
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
