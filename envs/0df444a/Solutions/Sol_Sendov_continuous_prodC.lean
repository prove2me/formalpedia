-- Prove2me | solution 1 for Sendov.continuous_prodC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:56:53.183378+00:00
-- url     : https://prove2.me/submissions/b002b68b-290c-4a1b-bc82-080668a9410a

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero


attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.Fprod_zero

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℝ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simpa using continuous_const
  | cons v r ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : Continuous fun t : ℝ => 1 - (a : ℂ) * (t : ℂ) * v).mul ih
end Sendov
