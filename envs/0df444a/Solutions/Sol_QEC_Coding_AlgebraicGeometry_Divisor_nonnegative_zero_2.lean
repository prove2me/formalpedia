-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.Divisor.nonnegative_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:34.512826+00:00
-- url     : https://prove2.me/submissions/7aa5f34f-1746-418c-9c8a-fdb3b78cfa94

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}
namespace QEC.Coding.AlgebraicGeometry.Divisor
theorem _root_.solution : Nonnegative (0 : Divisor P) := by
  intro P
  simp
end QEC.Coding.AlgebraicGeometry.Divisor
