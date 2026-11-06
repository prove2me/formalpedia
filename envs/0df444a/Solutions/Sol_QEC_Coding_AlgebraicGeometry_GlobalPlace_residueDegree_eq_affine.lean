-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:17:38.234297+00:00
-- url     : https://prove2.me/submissions/b038a366-17d9-4f57-a44b-e84f75b7b399

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
private theorem correctedTwoChartToGlobalPlace_inl_raw
    {k F : Type*} [Field k] [Finite k] [Field F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F]
    [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F] [κ : Algebra k F]
    (C : AffinePlace.carrier k F) :
    (correctedTwoChartToGlobalPlace (Sum.inl C : CorrectedTwoChartPlace k F)).valuation =
      (repackageRawGlobalPlace κ (AffinePlace.globalPlace k F C)).valuation := rfl
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
    (P : @GlobalPlace k F _ _ _ κ) (C : AffinePlace.carrier k F)
    (hvaluation : P.valuation =
      @GlobalPlace.valuation k F _ _ _ (AffinePlace.constantAlgebra k F)
        (AffinePlace.globalPlace k F C)) :
    GlobalPlace.residueDegree P = AffinePlace.residueDegree k F C := by
  unfold GlobalPlace.residueDegree
  have hpreimage : (chartGlobalPlaceEquiv (k := k) (F := F)).symm P = Sum.inl C := by
    apply (chartGlobalPlaceEquiv (k := k) (F := F)).injective
    rw [(chartGlobalPlaceEquiv (k := k) (F := F)).apply_symm_apply,
      chartGlobalPlaceEquiv_apply]
    apply globalPlace_eq_of_valuation_eq
    exact hvaluation.trans
      (correctedTwoChartToGlobalPlace_inl_raw (k := k) (F := F) C).symm
  rw [hpreimage]
  rfl
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
