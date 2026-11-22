-- Prove2me | solution 1 for SumProduct.idealCountArith_apply_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:47:22.202592+00:00
-- url     : https://prove2.me/submissions/b92f37ca-2970-4068-81e1-51567b2f073e

import Mathlib
import Definitions.Def_SumProduct_EulerBound

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    idealCountArith K n = idealCount K n := if_neg hn
end SumProduct
