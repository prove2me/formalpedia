-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_eq_denomDegree_sub_numDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:58:50.697499+00:00
-- url     : https://prove2.me/submissions/9a3bbc2f-8604-4c4b-9a00-0bd04775b941

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
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f =
      (f.denom.natDegree : ℤ) - f.num.natDegree := by
  rw [rationalInfinity_order_eq_neg_intDegree k f hf, RatFunc.intDegree]
  ring
end QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
