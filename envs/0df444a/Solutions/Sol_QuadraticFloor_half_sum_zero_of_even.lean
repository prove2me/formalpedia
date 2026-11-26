-- Prove2me | solution 1 for QuadraticFloor.half_sum_zero_of_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:43.401341+00:00
-- url     : https://prove2.me/submissions/a36692d0-7169-4178-8e3d-71d0936eab62

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_half_sum_zero_of_even__ebacac1c3808


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = -f x) (h0 : f 0 = 0)
    (hrefl : ∀ x ≤ 2 * h, f (2 * h - x) = f x) : ∑ x ∈ Icc 1 h, f x = 0 :=
  half_sum_zero_of_even' f hf h0 hrefl
end QuadraticFloor
