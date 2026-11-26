-- Prove2me | solution 1 for Sendov.continuous_sumEraseProdC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:14.696995+00:00
-- url     : https://prove2.me/submissions/4c6c85cd-c96e-4a87-bd6f-6dfb11565e8c

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProdC_cons
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_continuous_prodC
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero


attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.Fprod_zero

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℝ) (g : ℂ → ℂ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => sumEraseProdC q g (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    simp only [sumEraseProdC_zero]
    exact continuous_const
  | cons v r ih =>
    simp only [sumEraseProdC_cons]
    exact (continuous_const.mul (continuous_prodC a r)).add
      ((by fun_prop : Continuous fun t : ℝ => 1 - (a : ℂ) * (t : ℂ) * v).mul ih)
end Sendov
