-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.exists_infinityFibreGlobalPlace_of_inverseCoordinate_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:18:59.397209+00:00
-- url     : https://prove2.me/submissions/d7732353-72ec-4ec3-946f-1e9c564d65c9

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing


attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
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
    (P : @GlobalPlace k F _ _ _ κ)
    (hinv : P.valuation ((algebraMap (RatFunc k) F RatFunc.X)⁻¹) < 1) :
    ∃ D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F,
      P = InverseAffinePlace.infinityFibreGlobalPlace
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) D := by
  have hinv' : P.valuation (originalInverseCoordinate ρ) < 1 := by
    simpa only [originalInverseCoordinate, originalCoordinate] using hinv
  let D : InverseAffinePlace.infinityFibre (oldRationalAlgebra := ρ) k F :=
    inverseCentreInInfinityFibre
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) P hinv'
  refine ⟨D, ?_⟩
  apply globalPlace_eq_of_valuation_eq
  change P.valuation =
    @GlobalPlace.valuation k F _ _ _ κ
      (inverseFibreGlobalPlaceAt
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D)
  calc
    P.valuation = inverseFibreRawValuation
        (inverseCentreInInfinityFibre
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) P hinv') :=
      inverseCentre_rawValuation_eq_ambient
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (κ := κ) P hinv'
    _ = inverseFibreRawValuation D := by rfl
    _ = @GlobalPlace.valuation k F _ _ _ κ
        (inverseFibreGlobalPlaceAt
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D) :=
      (inverseFibreGlobalPlaceAt_valuation
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) κ D).symm
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
