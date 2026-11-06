-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_relNorm_spanSingleton_eq_intNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:43:42.867209+00:00
-- url     : https://prove2.me/submissions/23af4ab6-eaae-41e2-a652-9f407e73cf91

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



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
    Ideal.relNorm k[X] (Ideal.span ({x} : Set (directRingOfIntegers k F))) =
      Ideal.span ({Algebra.intNorm k[X] (directRingOfIntegers k F) x} : Set k[X]) := by
  letI : Module.Finite k[X] (directRingOfIntegers k F) :=
    AffinePlace.finite_ringOfIntegers k F
  letI : Module.IsTorsionFree k[X] F :=
    Module.IsTorsionFree.trans_faithfulSMul k[X] k⟮X⟯ F
  letI : Algebra.IsIntegral k[X] (directRingOfIntegers k F) :=
    IsIntegralClosure.isIntegral_algebra k[X] F
  simpa only using
    (Ideal.relNorm_singleton (R := k[X]) (S := directRingOfIntegers k F) x)
end QEC.Coding.AlgebraicGeometry.DirectNormCount
