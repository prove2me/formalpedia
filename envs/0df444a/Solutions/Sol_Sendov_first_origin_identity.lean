-- Prove2me | solution 1 for Sendov.first_origin_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:08.737195+00:00
-- url     : https://prove2.me/submissions/40b2288d-c24d-4286-9505-a2cc8a31f5f9

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_eval_prod_zero
import Theorems.Thm_Sendov_prod_inv_sub_mul
import Theorems.Thm_Sendov_eval_eq_integral
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open MeasureTheory
namespace Sendov
theorem _root_.solution {p : ℂ[X]} (hc0 : c ≠ 0) (ha0 : a ≠ 0)
    (hzcard : z.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0) (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (-1) ^ (n - 1) * q.prod * z.prod := by
  -- `p(0)` through the integral representation
  have hint : p.eval 0
      = -a * ∫ t in (0 : ℝ)..1,
          (n : ℂ) * c * (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod := by
    rw [eval_eq_integral hpa 0]
    congr 1
    · ring
    refine intervalIntegral.integral_congr ?_
    intro t _
    rw [hpq]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro v _
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    ring
  -- `p(0)` from the `z`-side
  have hev : p.eval 0 = c * (-a) * ((-1) ^ (n - 1) * z.prod) := by
    rw [hpz]
    simp only [eval_mul, eval_C, eval_sub, eval_X, zero_sub]
    rw [eval_prod_zero, hzcard]
    ring
  -- cancel `-a c` and clear the remaining denominator
  rw [intervalIntegral.integral_const_mul] at hint
  have hcancel : (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod
      = (-1) ^ (n - 1) * z.prod := by
    have hne : -a * c ≠ 0 := by simp [ha0, hc0]
    refine mul_left_cancel₀ hne ?_
    linear_combination hint.symm.trans hev
  calc (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => 1 - a * (t : ℂ) * v)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod * q.prod := by
        congr 1
        refine intervalIntegral.integral_congr ?_
        intro t _
        simp only []
        rw [prod_inv_sub_mul q hq0]
        refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
        intro v _
        ring
    _ = ((n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => v⁻¹ - (t : ℂ) * a)).prod) * q.prod := by
        rw [intervalIntegral.integral_mul_const]
        ring
    _ = ((-1) ^ (n - 1) * z.prod) * q.prod := by rw [hcancel]
    _ = (-1) ^ (n - 1) * q.prod * z.prod := by ring
end Sendov
