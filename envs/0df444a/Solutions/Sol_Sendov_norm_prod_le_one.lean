-- Prove2me | solution 1 for Sendov.norm_prod_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:54:19.921045+00:00
-- url     : https://prove2.me/submissions/7609596a-0eb0-4292-9c9c-910bce71cefd

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons v t ih =>
    intro hs
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [Multiset.prod_cons, norm_mul]
    nlinarith [ih ht, norm_nonneg v, norm_nonneg t.prod]
end Sendov
