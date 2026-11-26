-- Prove2me | solution 1 for Sendov.eval_prod_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:58:18.995114+00:00
-- url     : https://prove2.me/submissions/79bb1f14-5a67-4f42-a6f4-2e392ed7ee95

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution (u : ℂ) (s : Multiset ℂ) :
    ((s.map (fun w => X - C w)).prod).eval u = (s.map (fun w => u - w)).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun w _ => by simp)
end Sendov
