-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.direct_relNorm_span_coefficient_eq_sum_primesOver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:25:38.005609+00:00
-- url     : https://prove2.me/submissions/5b7814af-dd85-40ea-ba18-e0d2736c6ce2

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectRelNormCoefficient_direct_relNorm_coefficient_eq_sum_primesOver

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
open scoped BigOperators Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.directRelNormCoefficient_isTorsionFree
attribute [local instance] directRelNormCoefficient_isTorsionFree
namespace QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
theorem _root_.solution (x : B) (hx : x ≠ 0)
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Multiset.count p
        (normalizedFactors (Ideal.relNorm R (Ideal.span ({x} : Set B)))) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P *
          Multiset.count P (normalizedFactors (Ideal.span ({x} : Set B))) := by
  have hspan : Ideal.span ({x} : Set B) ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp hx
  exact direct_relNorm_coefficient_eq_sum_primesOver k F
    (Ideal.span ({x} : Set B)) hspan p hp0
end QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
