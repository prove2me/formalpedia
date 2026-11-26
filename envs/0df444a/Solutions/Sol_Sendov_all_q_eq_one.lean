-- Prove2me | solution 1 for Sendov.all_q_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:45.836929+00:00
-- url     : https://prove2.me/submissions/88951e80-36c4-4711-9988-72df789ffb8d

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
import Theorems.Thm_Sendov_half_le_re_inv_one_sub
import Theorems.Thm_Sendov_eq_one_of_re_eq_one_of_norm_le_one
import Theorems.Thm_Sendov_eq_zero_of_sum_eq_zero
import Theorems.Thm_Sendov_sum_le_card_mul
import Theorems.Thm_Sendov_card_mul_le_sum
import Theorems.Thm_Sendov_sum_map_one_sub_re
import Theorems.Thm_Sendov_sumEraseProd_zero
import Theorems.Thm_Sendov_sum_map_re
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial
namespace Sendov
theorem _root_.solution {N : ℕ} {qs zs : Multiset ℂ}
    (hqcard : qs.card = N) (hzcard : zs.card = N)
    (hq1 : ∀ v ∈ qs, ‖v‖ ≤ 1) (hz1 : ∀ w ∈ zs, ‖w‖ ≤ 1) (hzne : ∀ w ∈ zs, w ≠ 1)
    (hBR : qs.sum = 2 * (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum) :
    ∀ v ∈ qs, v = 1 := by
  have hupper : (qs.map (fun v => v.re)).sum ≤ (N : ℝ) := by
    have h := sum_le_card_mul 1 (qs.map (fun v => v.re)) (by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.1 hr
      exact (Complex.re_le_norm v).trans (hq1 v hv))
    rwa [Multiset.card_map, hqcard, mul_one] at h
  have hlower : (N : ℝ) ≤ (qs.map (fun v => v.re)).sum := by
    have h := card_mul_le_sum (1 / 2) (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)) (by
      intro r hr
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hr
      exact half_le_re_inv_one_sub (hz1 w hw) (hzne w hw))
    rw [Multiset.card_map, hzcard] at h
    have hmapre : (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)).sum
        = (zs.map (fun w => ((1 : ℂ) - w)⁻¹)).sum.re := by
      rw [← sum_map_re, Multiset.map_map]
      rfl
    have hre : (qs.map (fun v => v.re)).sum
        = 2 * (zs.map (fun w => (((1 : ℂ) - w)⁻¹).re)).sum := by
      rw [sum_map_re, hBR, hmapre, Complex.mul_re]
      simp
    rw [hre]
    linarith
  have heq : (qs.map (fun v => 1 - v.re)).sum = 0 := by
    rw [sum_map_one_sub_re, hqcard]
    linarith
  intro v hv
  refine eq_one_of_re_eq_one_of_norm_le_one ?_ (hq1 v hv)
  have hzero := eq_zero_of_sum_eq_zero (s := qs.map (fun v => 1 - v.re)) (by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.1 hr
    have := (Complex.re_le_norm u).trans (hq1 u hu)
    linarith) heq (1 - v.re) (Multiset.mem_map_of_mem _ hv)
  linarith
end Sendov
