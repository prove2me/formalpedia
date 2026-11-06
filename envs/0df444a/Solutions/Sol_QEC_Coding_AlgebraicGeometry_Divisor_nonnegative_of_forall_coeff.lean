-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.nonnegative_of_forall_coeff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:17:49.454793+00:00
-- url     : https://prove2.me/submissions/2374594f-b63b-4749-a1cf-df62aebe5294

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}

theorem solution {D : Divisor P} (hD : ∀ P, 0 ≤ D P) :
    Nonnegative D := by
  exact hD
