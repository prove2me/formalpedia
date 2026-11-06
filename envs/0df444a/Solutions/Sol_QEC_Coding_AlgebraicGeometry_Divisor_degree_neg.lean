-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.degree_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:58:45.641198+00:00
-- url     : https://prove2.me/submissions/efe512d7-00f1-44fe-b58b-99ef3a6b7bae

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
theorem _root_.solution (degreeOf : P → ℕ) (D : Divisor P) :
    degree degreeOf (-D) = -degree degreeOf D := by
  simpa [degree] using (degreeHom degreeOf).map_neg D
end QEC.Coding.AlgebraicGeometry.Divisor
