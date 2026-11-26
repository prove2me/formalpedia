-- Prove2me | solution 1 for Sendov.sumEraseProd_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:30.560826+00:00
-- url     : https://prove2.me/submissions/cdf1a631-622a-44b9-b8c5-db121d61f633

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
import Theorems.Thm_Sendov_norm_prod_le_one
import Theorems.Thm_Sendov_sumEraseProd_cons
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → s.prod = 0 →
    ‖sumEraseProd s‖ ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; simp at h
  | cons v t ih =>
    intro hs hp
    have hv := hs v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖u‖ ≤ 1 := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rw [sumEraseProd_cons]
    rcases eq_or_ne t.prod 0 with ht0 | ht0
    · rw [ht0, zero_add, norm_mul]
      nlinarith [ih ht ht0, norm_nonneg v, norm_nonneg (sumEraseProd t), hv]
    · have hv0 : v = 0 := by
        rw [Multiset.prod_cons] at hp
        rcases mul_eq_zero.1 hp with h | h
        · exact h
        · exact absurd h ht0
      rw [hv0, zero_mul, add_zero]
      exact norm_prod_le_one t ht
end Sendov
