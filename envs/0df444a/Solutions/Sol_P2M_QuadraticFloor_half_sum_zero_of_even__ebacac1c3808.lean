-- Prove2me | solution 1 for P2M_QuadraticFloor_half_sum_zero_of_even__ebacac1c3808
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:02.588792+00:00
-- url     : https://prove2.me/submissions/071d4837-a70c-484f-82e7-287ce8261280

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Theorems.Thm_QuadraticFloor_sum_Icc_one

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = -f x) (h0 : f 0 = 0)
    (hrefl : ∀ x ≤ 2 * h, f (2 * h - x) = f x) : ∑ x ∈ Icc 1 h, f x = 0 := by
  rw [sum_Icc_one]
  set T := ∑ k ∈ range h, f (k + 1)
  have hfh : f h = 0 := by have := hf 0; rw [zero_add, h0, neg_zero] at this; exact this
  -- reflect `k ↦ h - 1 - k`
  have hr := sum_range_reflect (fun k => f (k + 1)) h
  have hterm : ∀ j ∈ range h, f (h - 1 - j + 1) = -f j := by
    intro j hj
    have hj := mem_range.1 hj
    rw [show h - 1 - j + 1 = h - j by omega]
    have h1 := hf (h - j)
    rw [show h - j + h = 2 * h - j by omega, hrefl j (by omega)] at h1
    linear_combination h1
  rw [sum_congr rfl hterm, sum_neg_distrib] at hr
  have hshift : ∑ j ∈ range h, f j = T := by
    have a := sum_range_succ' f h
    have b := sum_range_succ f h
    rw [hfh, add_zero] at b
    rw [h0, add_zero] at a
    rw [← b, a]
  rw [hshift] at hr
  have : (2 : ℂ) * T = 0 := by linear_combination -hr
  simpa using this
end QuadraticFloor
