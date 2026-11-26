-- Prove2me | solution 1 for Sendov.card_mul_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:54.7455+00:00
-- url     : https://prove2.me/submissions/0a3e6afd-eb26-4230-962b-f4b2c8a5f770

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution (c : ℝ) : ∀ (s : Multiset ℝ), (∀ x ∈ s, c ≤ x) →
    (s.card : ℝ) * c ≤ s.sum := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro h
    have hv := h v (Multiset.mem_cons_self v t)
    have ht : ∀ x ∈ t, c ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]
end Sendov
