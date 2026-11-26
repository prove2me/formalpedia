-- Prove2me | solution 1 for Sendov.eval_deriv_prod_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:16.046018+00:00
-- url     : https://prove2.me/submissions/6f78a99c-3386-418d-9a12-a85e56696772

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
import Theorems.Thm_Sendov_eval_prod_at
import Theorems.Thm_Sendov_sumEraseProd_cons
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution (u : ℂ) : ∀ (s : Multiset ℂ),
    (derivative (s.map (fun w => X - C w)).prod).eval u
      = sumEraseProd (s.map (fun w => u - w)) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, derivative_mul, derivative_sub,
      derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C]
    rw [ih, eval_prod_at, sumEraseProd_cons]
end Sendov
