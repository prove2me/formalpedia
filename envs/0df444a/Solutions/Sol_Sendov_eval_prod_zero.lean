-- Prove2me | solution 1 for Sendov.eval_prod_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:01.356558+00:00
-- url     : https://prove2.me/submissions/ba09ca51-2a2e-4139-b347-6f414400067e

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_prod_map_neg
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
namespace Sendov
theorem _root_.solution (z : Multiset ℂ) :
    ((z.map (fun w => X - C w)).prod).eval 0 = (-1) ^ (Multiset.card z) * z.prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  rw [show (z.map ((fun r : ℂ[X] => r.eval 0) ∘ (fun w => X - C w))).prod
      = (z.map (fun w => -w)).prod from
    congrArg Multiset.prod (Multiset.map_congr rfl fun w _ => by simp)]
  exact prod_map_neg z
end Sendov
