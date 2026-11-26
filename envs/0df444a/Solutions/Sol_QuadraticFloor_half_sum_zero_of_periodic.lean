-- Prove2me | solution 1 for QuadraticFloor.half_sum_zero_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:30.838823+00:00
-- url     : https://prove2.me/submissions/22311873-3dba-4389-8c78-6c42533942fb

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_half_sum_zero_of_periodic__7707a5ec64ba


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (f : ℕ → ℂ) {h : ℕ} (hf : ∀ x, f (x + h) = f x)
    (hfull : ∑ x ∈ Icc 1 (2 * h), f x = 0) : ∑ x ∈ Icc 1 h, f x = 0 :=
  half_sum_zero_of_periodic' f hf hfull
end QuadraticFloor
