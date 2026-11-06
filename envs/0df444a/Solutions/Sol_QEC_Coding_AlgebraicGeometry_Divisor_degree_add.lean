-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.degree_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:16:28.941504+00:00
-- url     : https://prove2.me/submissions/a7d51de3-b7e1-4352-af99-e193e600d679

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
theorem _root_.solution (degreeOf : P → ℕ) (D E : Divisor P) :
    degree degreeOf (D + E) = degree degreeOf D + degree degreeOf E := by
  simpa [degree] using (degreeHom degreeOf).map_add D E
end QEC.Coding.AlgebraicGeometry.Divisor
