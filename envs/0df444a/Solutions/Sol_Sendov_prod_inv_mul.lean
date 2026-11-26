-- Prove2me | solution 1 for Sendov.prod_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:46.503878+00:00
-- url     : https://prove2.me/submissions/2f78b9ae-32a5-4288-b2d9-cf234385a066

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
    (q.map (fun v => v⁻¹)).prod * q.prod = 1 := by
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
