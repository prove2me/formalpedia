-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Divisor.Nonnegative.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:33:15.958736+00:00
-- url     : https://prove2.me/submissions/7f22de2e-500a-474a-8ca1-28eaded0d7f7

import Mathlib.Data.Finsupp.Weight
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open QEC.Coding.AlgebraicGeometry.Divisor
variable {P : Type*}
namespace QEC.Coding.AlgebraicGeometry.Divisor
namespace Nonnegative
theorem _root_.solution {D E : Divisor P} (hD : Nonnegative D) (hE : Nonnegative E) :
    Nonnegative (D + E) := by
  intro P
  exact add_nonneg (hD P) (hE P)
end Nonnegative
end QEC.Coding.AlgebraicGeometry.Divisor
