-- Prove2me | solution 1 for Sendov.prod_mul_sum_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:56:58.808947+00:00
-- url     : https://prove2.me/submissions/07c7d95f-701c-4eef-989a-b982dc551246

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
import Theorems.Thm_Sendov_sumEraseProd_cons
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution : ∀ (s : Multiset ℂ), (∀ w ∈ s, w ≠ 0) →
    s.prod * (s.map (fun w => w⁻¹)).sum = sumEraseProd s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp [sumEraseProd]
  | cons v t ih =>
    intro hs
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, u ≠ 0 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, sumEraseProd_cons, ← ih ht]
    field_simp
end Sendov
