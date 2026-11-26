-- Prove2me | solution 1 for Sendov.norm_sumEraseProdC_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:53.168834+00:00
-- url     : https://prove2.me/submissions/e7fe73e9-da6f-4a8f-acba-cc67b57e4ca4

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
import Theorems.Thm_Sendov_sumEraseProdMap_cons
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProdC_cons
import Theorems.Thm_Sendov_norm_prod_map
import Theorems.Thm_Sendov_prod_map_norm_nonneg
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero


attribute [local simp] Sendov.sumEraseProdC_zero

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (g f : ℂ → ℂ) : ∀ (s : Multiset ℂ), (∀ v ∈ s, ‖g v‖ ≤ 1) →
    ‖sumEraseProdC s g f‖ ≤ sumEraseProdMap s (fun v => ‖f v‖) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp [sumEraseProdMap]
  | cons v t ih =>
    intro hg
    have hv := hg v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖g u‖ ≤ 1 := fun u hu => hg u (Multiset.mem_cons_of_mem hu)
    rw [sumEraseProdC_cons, sumEraseProdMap_cons]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_prod_map]
    have h2 : (0 : ℝ) ≤ (t.map (fun v => ‖f v‖)).prod := prod_map_norm_nonneg t f
    nlinarith [ih ht, norm_nonneg (f v), norm_nonneg (sumEraseProdC t g f), h2, hv]
end Sendov
