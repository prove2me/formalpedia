-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.degree_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:16:41.475213+00:00
-- url     : https://prove2.me/submissions/ee6be475-eb26-4236-a3e2-3028687a1214

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
    degree degreeOf (D - E) = degree degreeOf D - degree degreeOf E := by
  simpa [degree] using (degreeHom degreeOf).map_sub D E
end QEC.Coding.AlgebraicGeometry.Divisor
