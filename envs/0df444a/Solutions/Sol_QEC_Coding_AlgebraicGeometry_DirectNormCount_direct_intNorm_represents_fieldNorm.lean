-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_intNorm_represents_fieldNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:43:43.748379+00:00
-- url     : https://prove2.me/submissions/4da6066d-1e19-4129-9d0d-1bc942164edd

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
theorem _root_.solution (x : directRingOfIntegers k F) :
    algebraMap k[X] k⟮X⟯ (Algebra.intNorm k[X] (directRingOfIntegers k F) x) =
      Algebra.norm k⟮X⟯ (algebraMap (directRingOfIntegers k F) F x) := by
  letI : Module.Finite k[X] (directRingOfIntegers k F) :=
    AffinePlace.finite_ringOfIntegers k F
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Algebra.IsIntegral k[X] (directRingOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  exact Algebra.algebraMap_intNorm x
end QEC.Coding.AlgebraicGeometry.DirectNormCount
