-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.finsupp_sum_eq_affine_add_infinityFibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:18:57.810198+00:00
-- url     : https://prove2.me/submissions/20e0d0b4-5b13-4089-b041-a88fccdf5db4

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

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution
    {k F M : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower k[X] (RatFunc k) F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable (RatFunc k) F]
    [AddCommMonoid M]
    (f : @GlobalPlace k F _ _ _ (AffinePlace.constantAlgebra k F) →₀ M) :
    f.sum (fun _ value => value) =
      (GlobalPlace.affineFinsupp (k := k) (F := F) f).sum
          (fun _ value => value) +
        (GlobalPlace.infinityFibreFinsupp
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
          (k := k) (F := F) f).sum (fun _ value => value) := by
  let e := chartGlobalPlaceEquiv
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
    (κ := AffinePlace.constantAlgebra k F)
  let c : CorrectedTwoChartPlace k F →₀ M :=
    Finsupp.equivMapDomain e.symm f
  have hc : c =
      (GlobalPlace.affineFinsupp (k := k) (F := F) f).sumElim
        (GlobalPlace.infinityFibreFinsupp
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
          (k := k) (F := F) f) := by
    ext C
    rcases C with C | D
    · rfl
    · change f (e (Sum.inr D)) =
        f (InverseAffinePlace.infinityFibreGlobalPlace
          (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
          (κ := AffinePlace.constantAlgebra k F) D)
      rfl
  calc
    f.sum (fun _ value => value) = c.sum (fun _ value => value) := by
      symm
      exact Finsupp.sum_equivMapDomain e.symm f (fun _ value => value)
    _ = ((GlobalPlace.affineFinsupp (k := k) (F := F) f).sumElim
          (GlobalPlace.infinityFibreFinsupp
            (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := σ)
            (k := k) (F := F) f)).sum (fun _ value => value) := by rw [hc]
    _ = _ := by
      simp only [Finsupp.sum, Finsupp.sumElim_support, Finset.sum_disjSum,
        Finsupp.sumElim_inl, Finsupp.sumElim_inr]
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
