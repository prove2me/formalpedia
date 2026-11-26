-- Prove2me | solution 1 for P2M_QuadraticFloor_half_sum_zero_of_periodic__7707a5ec64ba
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:59.066358+00:00
-- url     : https://prove2.me/submissions/ccc3cc2f-43c6-4993-8928-6b7e07a7c42c

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
theorem _root_.solution (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = f x)
    (hfull : ∑ x ∈ Icc 1 (2 * h), f x = 0) : ∑ x ∈ Icc 1 h, f x = 0 := by
  rw [sum_Icc_one, two_mul, sum_range_add] at hfull
  rw [sum_Icc_one]
  have : ∀ k ∈ range h, f (h + k + 1) = f (k + 1) := fun k _ => by
    rw [show h + k + 1 = (k + 1) + h by ring, hf]
  rw [sum_congr rfl this] at hfull
  have h2 : (2 : ℂ) * ∑ k ∈ range h, f (k + 1) = 0 := by rw [two_mul]; exact hfull
  simpa using h2
end QuadraticFloor
