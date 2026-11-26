-- Prove2me | solution 1 for Sendov.sum_map_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:56:53.830812+00:00
-- url     : https://prove2.me/submissions/6e9771bd-5c95-4f3a-90b0-ac92b236c1f2

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (s : Multiset ℂ) : (s.map (fun v => v.re)).sum = s.sum.re := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih => simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_re, ih]
end Sendov
