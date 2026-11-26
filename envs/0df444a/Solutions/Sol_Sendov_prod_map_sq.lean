-- Prove2me | solution 1 for Sendov.prod_map_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:13.975347+00:00
-- url     : https://prove2.me/submissions/2875f992-d793-4804-9761-48a9f9a128c0

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
theorem _root_.solution (s : Multiset ℂ) (f : ℂ → ℝ) :
    (s.map (fun v => f v ^ 2)).prod = ((s.map f).prod) ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih]
    ring
end Sendov
