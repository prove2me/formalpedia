-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalDivisor_inv
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:36:16.766312+00:00
-- url     : https://prove2.me/submissions/03aaabbc-5611-4a90-8803-cbad7edc4e8b

import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
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

theorem solution (f : Fˣ) :
    affinePrincipalDivisor k F f⁻¹ = -affinePrincipalDivisor k F f := by
  classical
  ext P
  change -(P.valuationOfNeZero f⁻¹).toAdd = -(-(P.valuationOfNeZero f).toAdd)
  simp
