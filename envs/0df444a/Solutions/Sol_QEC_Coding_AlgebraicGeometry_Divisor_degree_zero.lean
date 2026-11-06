-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:13.893981+00:00
-- url     : https://prove2.me/submissions/00801355-3c8b-4003-a2f9-1b771e35114e

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}
namespace QEC.Coding.AlgebraicGeometry.Divisor
theorem _root_.solution (degreeOf : P → ℕ) : degree degreeOf (0 : Divisor P) = 0 := by
  simpa [degree] using (degreeHom degreeOf).map_zero
end QEC.Coding.AlgebraicGeometry.Divisor
