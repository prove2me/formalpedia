-- Prove2me | solution 1 for QuadraticFloor.osum_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:58.355972+00:00
-- url     : https://prove2.me/submissions/73243594-d9cd-485e-aee5-5d2e6d6358e4

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (t c : ℤ) (g : ℤ → ℤ) : osum t (fun j => c * g j) = c * osum t g := by
  unfold osum; split_ifs <;> simp [mul_sum]
end QuadraticFloor
