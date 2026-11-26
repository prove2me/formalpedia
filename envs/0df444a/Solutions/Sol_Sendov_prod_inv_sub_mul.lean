-- Prove2me | solution 1 for Sendov.prod_inv_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:52:50.512655+00:00
-- url     : https://prove2.me/submissions/567ec866-f727-4787-8e2a-62546a87b51f

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
namespace Sendov
theorem _root_.solution : ∀ (q : Multiset ℂ), (∀ v ∈ q, v ≠ 0) →
    (q.map (fun v => v⁻¹ - a)).prod * q.prod = (q.map (fun v => 1 - a * v)).prod := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    intro hq
    have hv : v ≠ 0 := hq v (Multiset.mem_cons_self v t)
    have ht : ∀ w ∈ t, w ≠ 0 := fun w hw => hq w (Multiset.mem_cons_of_mem hw)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [← ih ht]
    field_simp
end Sendov
