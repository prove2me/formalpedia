-- Prove2me | solution 1 for Sendov.sum_norm_sq_one_sub_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:19.696204+00:00
-- url     : https://prove2.me/submissions/0c1052a1-c45c-4d7c-8403-b08c27e76c24

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_norm_sq_one_add_real_mul
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖1 + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) + 2 * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_one_add_real_mul]
    push_cast
    ring
end Sendov
