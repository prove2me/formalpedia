-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.count_chartFractionalLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:14.748202+00:00
-- url     : https://prove2.me/submissions/fdc70fc9-f7fb-419f-bc99-8c3eb842e9ef

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



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
theorem _root_.solution (D : Divisor (carrier k F)) (P : carrier k F) :
    FractionalIdeal.count F P (chartFractionalLattice k F D) = -D P := by
  simpa only [chartFractionalLattice, Finsupp.neg_apply] using
    (FractionalIdeal.count_finsuppProd F P (-D))
end QEC.Coding.AlgebraicGeometry.AffinePlace
