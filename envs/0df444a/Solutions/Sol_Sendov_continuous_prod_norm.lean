-- Prove2me | solution 1 for Sendov.continuous_prod_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:54:38.928876+00:00
-- url     : https://prove2.me/submissions/273ce15c-aadb-4e6a-863a-3b953e2f276b

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution (a : ℝ) (q : Multiset ℂ) :
    Continuous fun t : ℝ =>
      (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  induction q using Multiset.induction_on with
  | empty => simpa using continuous_const
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : Continuous fun t : ℝ =>
      ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖).mul ih
end Sendov
