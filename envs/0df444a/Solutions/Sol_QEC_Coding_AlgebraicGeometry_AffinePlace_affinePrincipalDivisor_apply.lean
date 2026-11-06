-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalDivisor_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:12:41.46252+00:00
-- url     : https://prove2.me/submissions/5539d870-5b18-4805-8938-c0d5b3e2215d

import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalCoefficient_eq_order

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
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_63657f3d4b_35
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (f : Fˣ) (P : carrier k F) :
    affinePrincipalDivisor k F f P = GlobalPlace.order (globalPlace k F P) (f : F) := by
  change affinePrincipalCoefficient k F P f = GlobalPlace.order (globalPlace k F P) (f : F)
  exact affinePrincipalCoefficient_eq_order k F P f
end QEC.Coding.AlgebraicGeometry.AffinePlace
