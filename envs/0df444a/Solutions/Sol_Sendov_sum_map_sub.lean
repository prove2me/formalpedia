-- Prove2me | solution 1 for Sendov.sum_map_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:16.483137+00:00
-- url     : https://prove2.me/submissions/94f3002a-e619-49e4-8025-ff98056faff3

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (s : Multiset ℂ) (f g : ℂ → ℂ) :
    (s.map (fun v => f v - g v)).sum = (s.map f).sum - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring
end Sendov
