-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_add_normalizedDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:49.940394+00:00
-- url     : https://prove2.me/submissions/845d3856-5d19-4f12-ac89-476adbc0aa9d

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_neg_intDegree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
open scoped RatFunc WithZero
variable (k : Type*) [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
theorem _root_.solution
    (f : RatFunc k) (hf : f ≠ 0) :
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f +
        ((f.num.natDegree : ℤ) - f.denom.natDegree) = 0 := by
  rw [rationalInfinity_order_eq_neg_intDegree k f hf, RatFunc.intDegree]
  ring
end QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
