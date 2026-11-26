-- Prove2me | solution 1 for Sendov.sum_norm_sq_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:54:19.361797+00:00
-- url     : https://prove2.me/submissions/93801d36-3bb8-4663-870a-575d99869f18

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
theorem _root_.solution (q : Multiset ℂ) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) :
    (q.map (fun v => ‖v‖ ^ 2)).sum ≤ (q.card : ℝ) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    have hv := hq1 v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hq1 u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    nlinarith [ih ht, norm_nonneg v]
end Sendov
