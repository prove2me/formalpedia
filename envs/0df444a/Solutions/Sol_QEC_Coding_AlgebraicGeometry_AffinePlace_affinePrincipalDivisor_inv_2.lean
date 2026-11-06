-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalDivisor_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:46.032196+00:00
-- url     : https://prove2.me/submissions/55b42b82-c657-48c1-bd8f-a6939f342d6e

import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_affinePrincipalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
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
theorem _root_.solution (f : Fˣ) :
    affinePrincipalDivisor k F f⁻¹ = -affinePrincipalDivisor k F f := by
  ext P
  simp only [Finsupp.neg_apply]
  rw [affinePrincipalDivisor_apply k F f⁻¹ P,
    affinePrincipalDivisor_apply k F f P]
  simpa using GlobalPlace.order_inv (globalPlace k F P) (f : F)
end QEC.Coding.AlgebraicGeometry.AffinePlace
