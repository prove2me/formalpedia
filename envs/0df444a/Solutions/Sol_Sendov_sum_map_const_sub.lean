-- Prove2me | solution 1 for Sendov.sum_map_const_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:20.256704+00:00
-- url     : https://prove2.me/submissions/1c70e8c9-a02d-466c-97c6-16df88b5ebe7

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (s : Multiset ℂ) (c : ℂ) (g : ℂ → ℂ) :
    (s.map (fun v => c - g v)).sum = (s.card : ℂ) * c - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring
end Sendov
