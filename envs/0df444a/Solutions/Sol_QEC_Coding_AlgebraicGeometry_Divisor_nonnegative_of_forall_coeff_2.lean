-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.Divisor.nonnegative_of_forall_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:33.52769+00:00
-- url     : https://prove2.me/submissions/18efc7bb-adfa-4595-9432-fc1427a4c135

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}
namespace QEC.Coding.AlgebraicGeometry.Divisor
theorem _root_.solution {D : Divisor P} (hD : ∀ P, 0 ≤ D P) :
    Nonnegative D := hD
end QEC.Coding.AlgebraicGeometry.Divisor
