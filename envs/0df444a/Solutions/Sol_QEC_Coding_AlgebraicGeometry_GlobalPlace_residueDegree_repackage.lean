-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.residueDegree_repackage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:32.886277+00:00
-- url     : https://prove2.me/submissions/b9034510-3056-4444-af1d-d02ddcd2450e

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
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (oldAlgebra newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) :
    @GlobalPlace.residueDegree k F _ _ _ π ρ τ φ σ newAlgebra
        (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
      @GlobalPlace.residueDegree k F _ _ _ π ρ τ φ σ oldAlgebra P := by
  let oldEquiv : CorrectedTwoChartPlace k F ≃
      @GlobalPlace k F _ _ _ oldAlgebra :=
    @chartGlobalPlaceEquiv k F _ _ _ π ρ τ φ σ oldAlgebra
  let newEquiv : CorrectedTwoChartPlace k F ≃
      @GlobalPlace k F _ _ _ newAlgebra :=
    @chartGlobalPlaceEquiv k F _ _ _ π ρ τ φ σ newAlgebra
  have hpreimage :
      newEquiv.symm
          (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
        oldEquiv.symm P := by
    apply newEquiv.injective
    rw [newEquiv.apply_symm_apply]
    apply globalPlace_eq_of_valuation_eq
    have hvaluation := congrArg
      (@GlobalPlace.valuation k F _ _ _ oldAlgebra)
      (oldEquiv.apply_symm_apply P)
    have hsame (C : CorrectedTwoChartPlace k F) :
        @GlobalPlace.valuation k F _ _ _ newAlgebra (newEquiv C) =
          @GlobalPlace.valuation k F _ _ _ oldAlgebra (oldEquiv C) := by
      calc
        @GlobalPlace.valuation k F _ _ _ newAlgebra (newEquiv C) =
            correctedTwoChartValuation C := by
          exact @correctedTwoChartToGlobalPlace_valuation
            k F _ _ _ π ρ τ φ σ newAlgebra C
        _ = @GlobalPlace.valuation k F _ _ _ oldAlgebra (oldEquiv C) := by
          symm
          exact @correctedTwoChartToGlobalPlace_valuation
            k F _ _ _ π ρ τ φ σ oldAlgebra C
    calc
      @GlobalPlace.valuation k F _ _ _ newAlgebra
          (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
          @GlobalPlace.valuation k F _ _ _ oldAlgebra P := rfl
      _ = @GlobalPlace.valuation k F _ _ _ oldAlgebra
          (oldEquiv (oldEquiv.symm P)) := hvaluation.symm
      _ = @GlobalPlace.valuation k F _ _ _ newAlgebra
          (newEquiv (oldEquiv.symm P)) := (hsame _).symm
  change twoChartResidueDegree (k := k) (F := F)
      (newEquiv.symm
        (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P)) =
    twoChartResidueDegree (k := k) (F := F) (oldEquiv.symm P)
  rw [hpreimage]
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
