-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_sum_ramification_inertia
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:08.010797+00:00
-- url     : https://prove2.me/submissions/1882e8cf-38f2-4c9f-9b62-f605e43f795f

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectNormCount
open scoped Polynomial RatFunc nonZeroDivisors
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectNormCount._p2m_local_instance_154c3067f1_22
namespace QEC.Coding.AlgebraicGeometry.DirectNormCount
theorem _root_.solution
    {p : Ideal k[X]} [p.IsMaximal] (hp : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p (directRingOfIntegers k F),
      p.ramificationIdx' P * p.inertiaDeg' P = Module.finrank k⟮X⟯ F := by
  letI : Module.Finite k[X] (directRingOfIntegers k F) :=
    AffinePlace.finite_ringOfIntegers k F
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Algebra.IsIntegral k[X] (directRingOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  exact Ideal.sum_ramification_inertia (directRingOfIntegers k F) k⟮X⟯ F hp
end QEC.Coding.AlgebraicGeometry.DirectNormCount
