-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:41:01.230944+00:00
-- url     : https://prove2.me/submissions/0be85518-ded0-4d98-9823-f3a432730e03

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_placeDivisor_degree


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F ι : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution [Fintype ι]
    (P : ι → GlobalPlace k F) :
    Divisor.degree (residueDegree (k := k) (F := F))
        (finitePlaceDivisor P) =
      ∑ i : ι, (residueDegree (k := k) (F := F) (P i) : ℤ) := by
  classical
  unfold finitePlaceDivisor
  change
    Divisor.degreeHom (residueDegree (k := k) (F := F))
        (∑ i : ι, placeDivisor (P i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact placeDivisor_degree (P i)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
