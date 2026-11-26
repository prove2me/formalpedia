-- Prove2me | solution 1 for Sendov.second_origin_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:02.251872+00:00
-- url     : https://prove2.me/submissions/a178cbd4-2fa9-4337-ab97-3503712242b7

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_eval_prod_zero
import Theorems.Thm_Sendov_eval_deriv_prod_zero
import Theorems.Thm_Sendov_prod_inv_sub_mul
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open scoped Classical
namespace Sendov
theorem _root_.solution {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by
  -- `p'(0)` from the `q`-side
  have hev1 : (derivative p).eval 0 = (n : ℂ) * c * (q.map (fun v => v⁻¹ - a)).prod := by
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp
  -- `p'(0)` from the `z`-side
  have hev2 : (derivative p).eval 0
      = c * ((-1) ^ (n - 1) * (z.prod + a * sumEraseProd z)) := by
    rw [hpz, derivative_C_mul, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp only [eval_mul, eval_C, eval_add, eval_sub, eval_X, sub_zero, zero_sub, one_mul]
    rw [eval_deriv_prod_zero, eval_prod_zero, hzcard]
    ring
  -- combine and clear the denominators
  have hcancel : (n : ℂ) * (q.map (fun v => v⁻¹ - a)).prod
      = (-1) ^ (n - 1) * (z.prod + a * sumEraseProd z) := by
    refine mul_left_cancel₀ hc0 ?_
    linear_combination hev1.symm.trans hev2
  calc (n : ℂ) * (q.map (fun v => 1 - a * v)).prod
      = (n : ℂ) * ((q.map (fun v => v⁻¹ - a)).prod * q.prod) := by
        rw [prod_inv_sub_mul q hq0]
    _ = ((n : ℂ) * (q.map (fun v => v⁻¹ - a)).prod) * q.prod := by ring
    _ = ((-1) ^ (n - 1) * (z.prod + a * sumEraseProd z)) * q.prod := by rw [hcancel]
    _ = (-1) ^ (n - 1) * q.prod * (z.prod + a * sumEraseProd z) := by ring
end Sendov
