-- Prove2me | solution 1 for Sendov.sum_norm_sq_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:59.107633+00:00
-- url     : https://prove2.me/submissions/8ad25b37-87b9-42bc-b32a-15b669230373

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_norm_sq_add_real_mul
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution (a s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) * a ^ 2 + 2 * a * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_add_real_mul]
    push_cast
    ring
end Sendov
