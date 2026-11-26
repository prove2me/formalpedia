-- Prove2me | solution 1 for Sendov.sum_map_one_sub_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:59.440942+00:00
-- url     : https://prove2.me/submissions/a0dc2362-acd0-475f-8c89-b2a939a99466

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
theorem _root_.solution (s : Multiset ℂ) :
    (s.map (fun v => 1 - v.re)).sum = (s.card : ℝ) - (s.map (fun v => v.re)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring
end Sendov
