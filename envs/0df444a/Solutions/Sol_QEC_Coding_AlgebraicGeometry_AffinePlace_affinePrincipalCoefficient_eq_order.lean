-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.affinePrincipalCoefficient_eq_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:11:31.584782+00:00
-- url     : https://prove2.me/submissions/958a2b13-957e-4945-9604-7322b99f7fca

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
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (P : carrier k F) (f : Fˣ) :
    affinePrincipalCoefficient k F P f =
      GlobalPlace.order (globalPlace k F P) (f : F) := by
  change -(P.valuationOfNeZero f).toAdd = -WithZero.log (valuation k F P (f : F))
  exact congrArg (fun x : ℤᵐ⁰ => -WithZero.log x) (P.valuationOfNeZero_eq f)
end QEC.Coding.AlgebraicGeometry.AffinePlace
