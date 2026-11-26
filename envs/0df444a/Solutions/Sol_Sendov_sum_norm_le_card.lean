-- Prove2me | solution 1 for Sendov.sum_norm_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:41.435644+00:00
-- url     : https://prove2.me/submissions/80123392-ee7f-47a5-92c4-58e81b260660

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.Fprod_zero
attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution : ∀ (q : Multiset ℂ), (∀ v ∈ q, ‖v‖ ≤ 1) →
    (q.map (fun v => ‖v‖)).sum ≤ (q.card : ℝ) := by
  intro q
  induction q using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro hq
    have hv := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hq u (Multiset.mem_cons_of_mem hu)
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [ih ht]
end Sendov
