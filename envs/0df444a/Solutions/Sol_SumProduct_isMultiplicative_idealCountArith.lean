-- Prove2me | solution 1 for SumProduct.isMultiplicative_idealCountArith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:04.217272+00:00
-- url     : https://prove2.me/submissions/da67cd0d-8100-456b-93ed-12d9928f6d12

import Mathlib
import Definitions.Def_SumProduct_EulerBound
import Theorems.Thm_SumProduct_idealCount_one
import Theorems.Thm_SumProduct_idealCount_mul_of_coprime
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
attribute [local simp] SumProduct.idealCountArith_apply_ne

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution : (idealCountArith K).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [idealCount_one], fun {m n} hm hn hmn => ?_⟩
  simp only [idealCountArith_apply_ne hm, idealCountArith_apply_ne hn,
    idealCountArith_apply_ne (mul_ne_zero hm hn)]
  exact idealCount_mul_of_coprime hmn hm hn
end SumProduct
