-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalDivisor_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:44.864338+00:00
-- url     : https://prove2.me/submissions/d218518f-ccea-41f7-aef6-27771558f0bd

import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_63657f3d4b_35
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (f g : Fˣ) :
    affinePrincipalDivisor k F (f * g) =
      affinePrincipalDivisor k F f + affinePrincipalDivisor k F g := by
  ext P
  simp only [Finsupp.add_apply]
  rw [affinePrincipalDivisor_apply k F (f * g) P,
    affinePrincipalDivisor_apply k F f P,
    affinePrincipalDivisor_apply k F g P]
  simpa using GlobalPlace.order_mul (globalPlace k F P)
    (f := (f : F)) (g := (g : F)) f.ne_zero g.ne_zero
end QEC.Coding.AlgebraicGeometry.AffinePlace
