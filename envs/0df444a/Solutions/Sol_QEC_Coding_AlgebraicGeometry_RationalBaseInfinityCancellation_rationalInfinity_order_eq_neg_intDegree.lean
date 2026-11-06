-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation.rationalInfinity_order_eq_neg_intDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:44:22.990499+00:00
-- url     : https://prove2.me/submissions/d0b0f26a-30a3-4af5-95e1-9a708f809cdf

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
open scoped RatFunc WithZero
variable (k : Type*) [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
theorem _root_.solution (f : RatFunc k) (hf : f ≠ 0) :
    GlobalPlace.order (GlobalPlace.rationalInfinity k) f = -f.intDegree := by
  classical
  change -WithZero.log (RatFunc.inftyValuation k f) = -f.intDegree
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero (F := k) hf,
    WithZero.log_exp]
end QEC.Coding.AlgebraicGeometry.RationalBaseInfinityCancellation
