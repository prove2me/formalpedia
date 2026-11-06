-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.chartFractionalLattice_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:15.535902+00:00
-- url     : https://prove2.me/submissions/fe76323f-4d12-4557-8e51-4e294930cff4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero nonZeroDivisors
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_45ffe40864_30
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (D : Divisor (carrier k F)) :
    chartFractionalLattice k F D ≠ 0 := by
  classical
  rw [chartFractionalLattice, Finsupp.prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot)
end QEC.Coding.AlgebraicGeometry.AffinePlace
