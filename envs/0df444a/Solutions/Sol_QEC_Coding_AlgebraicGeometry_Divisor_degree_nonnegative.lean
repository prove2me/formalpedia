-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.degree_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:21:48.285289+00:00
-- url     : https://prove2.me/submissions/f3bdf9ba-570e-4871-85c8-b2af36fb9de3

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}
namespace QEC.Coding.AlgebraicGeometry.Divisor
theorem _root_.solution (degreeOf : P → ℕ) (D : Divisor P) (hD : Nonnegative D) :
    0 ≤ degree degreeOf D := by
  change 0 ≤ D.sum fun P coefficient => coefficient * (degreeOf P : ℤ)
  exact Finsupp.sum_nonneg fun P _ => mul_nonneg (hD P) (Int.ofNat_nonneg _)
end QEC.Coding.AlgebraicGeometry.Divisor
