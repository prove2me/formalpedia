-- Prove2me | solution 1 for Sendov.sumEraseProd_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:53:30.430822+00:00
-- url     : https://prove2.me/submissions/99c90f4f-f257-4124-8fae-fc56f3342c39

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open scoped Classical
namespace Sendov
theorem _root_.solution (v : ℂ) (t : Multiset ℂ) :
    sumEraseProd (v ::ₘ t) = t.prod + v * sumEraseProd t := by
  simp only [sumEraseProd, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.prod_cons]
end Sendov
