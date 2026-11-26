-- Prove2me | solution 1 for Sendov.eval_deriv_prod_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:38.350786+00:00
-- url     : https://prove2.me/submissions/973b4ff2-39f6-40d7-a137-1324c40daf4f

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_sumEraseProd_cons
import Theorems.Thm_Sendov_eval_prod_zero
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
namespace Sendov
theorem _root_.solution : ∀ (z : Multiset ℂ),
    (derivative (z.map (fun w => X - C w)).prod).eval 0
      = -((-1) ^ (Multiset.card z) * sumEraseProd z) := by
  intro z
  induction z using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, zero_sub, Multiset.card_cons]
    rw [ih, eval_prod_zero, sumEraseProd_cons]
    ring
end Sendov
