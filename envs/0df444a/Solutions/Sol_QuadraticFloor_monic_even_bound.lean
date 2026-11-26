-- Prove2me | solution 1 for QuadraticFloor.monic_even_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:24.084814+00:00
-- url     : https://prove2.me/submissions/61093fb3-07e4-4c18-99b6-a59be9fb9a97

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_monic_even_bound__299c38c9066e


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (t b : ℤ) :
    |floorSum 1 (2 * t) b p| ≤ 1 + 2 * |t| :=
  monic_even_bound' hp2 t b
end QuadraticFloor
