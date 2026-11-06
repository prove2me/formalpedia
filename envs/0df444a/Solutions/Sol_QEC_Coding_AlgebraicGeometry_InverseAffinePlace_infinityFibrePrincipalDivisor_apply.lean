-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibrePrincipalDivisor_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:17:58.953781+00:00
-- url     : https://prove2.me/submissions/37b063f5-2ba1-4e55-8eec-df27360235e4

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing


section
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
namespace QEC.Coding.AlgebraicGeometry
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
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
namespace InverseAffinePlace
theorem _root_.solution
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) (D : InverseAffinePlace.infinityFibre k F) :
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
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    InverseAffinePlace.infinityFibrePrincipalDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (k := k) (F := F) f D =
      GlobalPlace.order (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
        (oldFunctionField := φ) (oldSeparable := σ) k F D) (f : F) := by
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
  letI : Algebra k F := AffinePlace.constantAlgebra k F
  change inverseFibrePrincipalDivisor
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ) (k := k) (F := F) f D =
    GlobalPlace.order (InverseAffinePlace.globalPlace (oldRationalAlgebra := ρ)
      (oldFunctionField := φ) (oldSeparable := σ) k F D) (f : F)
  rw [inverseFibrePrincipalDivisor_apply
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)]
  rfl
end InverseAffinePlace
end QEC.Coding.AlgebraicGeometry
