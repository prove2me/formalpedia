-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_eq_inverseFibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:18:03.687206+00:00
-- url     : https://prove2.me/submissions/768f7572-e05b-4ccc-9237-ad18d42cd8b0

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
    (P : @GlobalPlace k F _ _ _ κ) (D : InverseAffinePlace.infinityFibre k F)
    (hvaluation : @GlobalPlace.valuation k F _ _ _ κ P =
      @GlobalPlace.valuation k F _ _ _ κ (inverseFibreGlobalPlaceAt κ D)) :
    GlobalPlace.residueDegree P =
      InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F) D := by
  unfold GlobalPlace.residueDegree
  have hpreimage : (chartGlobalPlaceEquiv (k := k) (F := F)).symm P = Sum.inr D := by
    apply (chartGlobalPlaceEquiv (k := k) (F := F)).injective
    rw [(chartGlobalPlaceEquiv (k := k) (F := F)).apply_symm_apply,
      chartGlobalPlaceEquiv_apply]
    apply globalPlace_eq_of_valuation_eq
    exact hvaluation.trans
      (correctedTwoChartToGlobalPlace_inr_raw (k := k) (F := F) D).symm
  rw [hpreimage]
  rfl
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
