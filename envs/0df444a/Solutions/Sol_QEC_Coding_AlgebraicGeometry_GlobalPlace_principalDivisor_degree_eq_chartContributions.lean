-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_degree_eq_chartContributions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:00.127993+00:00
-- url     : https://prove2.me/submissions/ec5a73e2-d383-4059-970c-51eef046a1d0

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
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
private theorem divisor_degree_equivMapDomain
    {α β : Type*} (e : α ≃ β) (weight : β → ℕ) (D : Divisor α) :
    Divisor.degree weight (Finsupp.equivMapDomain e D) =
      Divisor.degree (fun a => weight (e a)) D := by
  change (Finsupp.equivMapDomain e D).sum
      (fun b coefficient => coefficient * (weight b : ℤ)) =
    D.sum (fun a coefficient => coefficient * (weight (e a) : ℤ))
  rw [Finsupp.sum_equivMapDomain]
private theorem divisor_degree_sum_mapDomain
    {α β : Type*} (left : Divisor α) (right : Divisor β)
    (weight : Sum α β → ℕ) :
    Divisor.degree weight
        (Finsupp.mapDomain Sum.inl left + Finsupp.mapDomain Sum.inr right) =
      Divisor.degree (fun a => weight (Sum.inl a)) left +
        Divisor.degree (fun b => weight (Sum.inr b)) right := by
  rw [Divisor.degree_add]
  change (Finsupp.mapDomain Sum.inl left).sum
      (fun q coefficient => coefficient * (weight q : ℤ)) +
    (Finsupp.mapDomain Sum.inr right).sum
      (fun q coefficient => coefficient * (weight q : ℤ)) =
    left.sum (fun a coefficient => coefficient * (weight (Sum.inl a) : ℤ)) +
      right.sum (fun b coefficient => coefficient * (weight (Sum.inr b) : ℤ))
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
        (fun _ _ _ => by simp [add_mul])]
private theorem principalDivisor_degree_eq_twoChart_degree
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (f : Fˣ) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (GlobalPlace.principalDivisor (k := k) (F := F) f) =
      Divisor.degree (twoChartResidueDegree (k := k) (F := F))
        (twoChartPrincipalDivisor (k := k) (F := F) f) := by
  unfold GlobalPlace.principalDivisor
  let e := chartGlobalPlaceEquiv (k := k) (F := F)
  have hweight : ∀ C : CorrectedTwoChartPlace k F,
      GlobalPlace.residueDegree (e C) = twoChartResidueDegree (k := k) (F := F) C := by
    intro C
    change twoChartResidueDegree (k := k) (F := F) (e.symm (e C)) =
      twoChartResidueDegree (k := k) (F := F) C
    rw [e.symm_apply_apply]
  calc
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (Finsupp.equivMapDomain e (twoChartPrincipalDivisor (k := k) (F := F) f)) =
      Divisor.degree (fun C => GlobalPlace.residueDegree (e C))
        (twoChartPrincipalDivisor (k := k) (F := F) f) :=
      divisor_degree_equivMapDomain e (GlobalPlace.residueDegree (k := k) (F := F))
        (twoChartPrincipalDivisor (k := k) (F := F) f)
    _ = Divisor.degree (twoChartResidueDegree (k := k) (F := F))
        (twoChartPrincipalDivisor (k := k) (F := F) f) := by
      rw [show (fun C => GlobalPlace.residueDegree (e C)) =
        twoChartResidueDegree (k := k) (F := F) from funext hweight]
private theorem twoChart_principalDivisor_degree_split
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (f : Fˣ) :
    Divisor.degree (twoChartResidueDegree (k := k) (F := F))
        (twoChartPrincipalDivisor (k := k) (F := F) f) =
      Divisor.degree (AffinePlace.residueDegree k F)
        (AffinePlace.affinePrincipalDivisor k F f) +
      Divisor.degree (inverseFibreResidueDegree (k := k) (F := F))
        (inverseFibrePrincipalDivisor (k := k) (F := F) f) := by
  unfold twoChartPrincipalDivisor
  exact divisor_degree_sum_mapDomain
    (AffinePlace.affinePrincipalDivisor k F f)
    (inverseFibrePrincipalDivisor (k := k) (F := F) f)
    (twoChartResidueDegree (k := k) (F := F))
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
    (f : Fˣ) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
        (GlobalPlace.principalDivisor (k := k) (F := F) f) =
      Divisor.degree (AffinePlace.residueDegree k F)
        (AffinePlace.affinePrincipalDivisor k F f) +
      Divisor.degree (InverseAffinePlace.infinityFibreResidueDegree (k := k) (F := F))
        (InverseAffinePlace.infinityFibrePrincipalDivisor (k := k) (F := F) f) := by
  rw [principalDivisor_degree_eq_twoChart_degree,
    twoChart_principalDivisor_degree_split]
  rfl
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
