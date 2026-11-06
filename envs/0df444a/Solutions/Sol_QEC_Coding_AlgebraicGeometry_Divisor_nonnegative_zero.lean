-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.nonnegative_zero
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:40:16.928201+00:00
-- url     : https://prove2.me/submissions/48aca5d9-215e-45fb-b56f-8bb43ab63562

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}
theorem solution : Nonnegative (0 : Divisor P) := by
  intro p
  simp only [Finsupp.coe_zero, Pi.zero_apply, le_refl]
