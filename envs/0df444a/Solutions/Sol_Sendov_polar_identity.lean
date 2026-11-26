-- Prove2me | solution 1 for Sendov.polar_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:19.770644+00:00
-- url     : https://prove2.me/submissions/30f066b7-6474-49b7-b8f8-f08d9562db92

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_eval_eq_integral
import Theorems.Thm_Sendov_prod_map_mul_const
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open MeasureTheory
namespace Sendov
theorem _root_.solution (hc0 : c ≠ 0) (ha0 : a ≠ 0) (ha2 : a ^ 2 ≠ 1)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1) (hq0 : ∀ v ∈ q, v ≠ 0)
    (hpa : p.eval a = 0)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    q.prod * (z.map (fun w => 1 - a * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod := by
  have hinv : a⁻¹ - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    apply ha2
    field_simp at h
    linear_combination -h
  -- `p(1/a)` through the integral representation
  have hint : p.eval a⁻¹
      = (a⁻¹ - a) * ((n : ℂ) * c * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod) := by
    rw [eval_eq_integral hpa a⁻¹]
    congr 1
    have hcong : (∫ t in (0 : ℝ)..1, (derivative p).eval (a + (t : ℂ) * (a⁻¹ - a)))
        = ∫ t in (0 : ℝ)..1,
            (n : ℂ) * c * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      simp only []
      rw [hpq]
      simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
      congr 1
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro v _
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
      ring
    rw [hcong, intervalIntegral.integral_const_mul]
  -- `p(1/a)` from the `z`-side
  have hev : p.eval a⁻¹ = c * ((a⁻¹ - a) * (z.map (fun w => a⁻¹ - w)).prod) := by
    rw [hpz]
    simp only [eval_mul, eval_C, eval_sub, eval_X, eval_multiset_prod, Multiset.map_map]
    congr 2
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    simp
  -- cancel `c (1/a - a)`
  have hcancel : (z.map (fun w => a⁻¹ - w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1, (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
    have hne : c * (a⁻¹ - a) ≠ 0 := mul_ne_zero hc0 hinv
    refine mul_left_cancel₀ hne ?_
    linear_combination hev.symm.trans hint
  -- restore the two products
  have hLHS : (z.map (fun w => 1 - a * w)).prod
      = a ^ (n - 1) * (z.map (fun w => a⁻¹ - w)).prod := by
    rw [← hzcard, ← prod_map_mul_const a z (fun w => a⁻¹ - w)]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro w _
    field_simp
  have hRHS : ∀ t : ℝ, (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod
      = a ^ (n - 1) * q.prod * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
    intro t
    have h1 : (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod
        = (q.map (fun v => a * (v * ((t : ℂ) * (a⁻¹ - a) + v⁻¹)))).prod := by
      refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
      intro v hv
      have hv0 : v ≠ 0 := hq0 v hv
      field_simp
      ring
    rw [h1, prod_map_mul_const a q (fun v => v * ((t : ℂ) * (a⁻¹ - a) + v⁻¹)),
      Multiset.prod_map_mul, hqcard]
    have : (q.map (fun v => v)).prod = q.prod := by rw [Multiset.map_id']
    rw [this]
    ring
  rw [hLHS]
  calc q.prod * (a ^ (n - 1) * (z.map (fun w => a⁻¹ - w)).prod)
      = a ^ (n - 1) * q.prod
          * ((n : ℂ) * ∫ t in (0 : ℝ)..1,
              (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod) := by
        rw [hcancel]; ring
    _ = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          a ^ (n - 1) * q.prod * (q.map (fun v => (t : ℂ) * (a⁻¹ - a) + v⁻¹)).prod := by
        rw [intervalIntegral.integral_const_mul]; ring
    _ = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => a + (t : ℂ) * (1 - a ^ 2) * v)).prod := by
        congr 1
        refine intervalIntegral.integral_congr ?_
        intro t _
        simp only []
        rw [hRHS t]
end Sendov
