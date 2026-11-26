-- Prove2me | solution 1 for Sendov.prod_sub_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:19.216463+00:00
-- url     : https://prove2.me/submissions/22c7dd8a-77f7-4bbc-be94-3873db8f2922

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_prod_inv_mul
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
namespace Sendov
theorem _root_.solution (hc0 : c ≠ 0) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => a - w)).prod = (n : ℂ) := by
  have hev1 : (derivative p).eval a = (n : ℂ) * c * (q.map (fun v => v⁻¹)).prod := by
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  have hev2 : (derivative p).eval a = c * (z.map (fun w => a - w)).prod := by
    rw [hpz, derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_zero, sub_self, zero_mul,
      add_zero, one_mul, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    simp
  have hcancel : (z.map (fun w => a - w)).prod = (n : ℂ) * (q.map (fun v => v⁻¹)).prod := by
    refine mul_left_cancel₀ hc0 ?_
    linear_combination hev2.symm.trans hev1
  calc q.prod * (z.map (fun w => a - w)).prod
      = q.prod * ((n : ℂ) * (q.map (fun v => v⁻¹)).prod) := by rw [hcancel]
    _ = (n : ℂ) * ((q.map (fun v => v⁻¹)).prod * q.prod) := by ring
    _ = (n : ℂ) := by rw [prod_inv_mul q hq0]; ring
end Sendov
