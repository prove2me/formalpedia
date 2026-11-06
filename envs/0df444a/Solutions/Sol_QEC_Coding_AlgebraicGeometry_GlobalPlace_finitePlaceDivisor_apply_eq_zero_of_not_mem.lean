-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:06:05.823196+00:00
-- url     : https://prove2.me/submissions/daf7f648-f238-4c1f-8f4d-3dc7b6b6caeb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor

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
    (P : ι → GlobalPlace k F) (Q : GlobalPlace k F)
    (hQ : Q ∉ Set.range P) : finitePlaceDivisor P Q = 0 := by
  classical
  unfold finitePlaceDivisor
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply placeDivisor_apply_of_ne
  intro hPi
  exact hQ ⟨i, hPi⟩
end QEC.Coding.AlgebraicGeometry.GlobalPlace
