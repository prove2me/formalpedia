-- Prove2me | solution 1 for Sendov.xy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:05:22.275301+00:00
-- url     : https://prove2.me/submissions/b4740644-7de9-49f6-816c-4701380e6efd

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
import Theorems.Thm_Sendov_sum_norm_le_card
import Theorems.Thm_Sendov_Fprod_zero
import Theorems.Thm_Sendov_norm_sum_map_le
import Theorems.Thm_Sendov_sumEraseProdC_zero
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_sum_map_re
attribute [local simp] Sendov.Fprod_zero
attribute [local simp] Sendov.sumEraseProdC_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I)) :
    (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x ∧ x ^ 2 + y ^ 2 ≤ 1 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnc : ‖((n : ℂ) - 1)‖ = (n : ℝ) - 1 := by
    have hc : ((n : ℂ) - 1) = (((n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hn1)]
  have hqcardR : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  refine ⟨?_, ?_⟩
  · have hc : ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * I)
        = ((((n : ℝ) - 1) * x : ℝ) : ℂ) + ((((n : ℝ) - 1) * y : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [sum_map_re, hxy, hc]
    simp
  · have hxynorm : ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    have h2 : ‖q.sum‖ ≤ (q.map (fun v => ‖v‖)).sum := by
      have h := norm_sum_map_le q (fun v => v)
      simpa using h
    have h3 := sum_norm_le_card q hq1
    rw [hqcardR] at h3
    have h1 : ‖q.sum‖ ≤ (n : ℝ) - 1 := h2.trans h3
    rw [hxy, norm_mul, hnc] at h1
    have h4 : ‖(x : ℂ) + (y : ℂ) * I‖ ≤ 1 := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith [h1, hn1]
    nlinarith [hxynorm, h4, norm_nonneg ((x : ℂ) + (y : ℂ) * I)]
end Sendov
