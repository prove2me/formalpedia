-- Prove2me | solution 1 for SumProduct.isMultiplicative_zeta_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:02:10.012603+00:00
-- url     : https://prove2.me/submissions/f52071c5-2581-4bdb-8797-3f6ad7e8efda

import Mathlib
import Definitions.Def_SumProduct_EulerBound

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution (d : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d).IsMultiplicative := by
  induction d with
  | zero => rw [pow_zero]; exact ArithmeticFunction.isMultiplicative_one
  | succ d ih => rw [pow_succ]; exact ih.mul ArithmeticFunction.isMultiplicative_zeta
end SumProduct
