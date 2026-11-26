-- Prove2me | solution 1 for Sendov.sumEraseProdC_id_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:59.971476+00:00
-- url     : https://prove2.me/submissions/4a4a5367-aefd-4005-b670-33cdcd1afce8

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProdC_cons
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero


attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.Fprod_zero

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a t : ℝ) : ∀ (q : Multiset ℂ),
    sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
      = q.sum * Fprod a q t
        + (a : ℂ) * (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
            (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp [Fprod]
  | cons v r ih =>
    rw [sumEraseProdC_cons, sumEraseProdC_cons, ih, Multiset.sum_cons]
    simp only [Fprod, Multiset.map_cons, Multiset.prod_cons, id]
    ring
end Sendov
