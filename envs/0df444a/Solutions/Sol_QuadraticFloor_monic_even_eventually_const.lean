-- Prove2me | solution 1 for QuadraticFloor.monic_even_eventually_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:31.656803+00:00
-- url     : https://prove2.me/submissions/d5adc997-9484-4577-9789-a99e6314b71f

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_monic_even_eventually_const__f9067cd031a4


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (t b : ℤ) :
    ∃ N : ℕ, ∃ c : ℤ, ∀ p : ℕ, p.Prime → N < p → floorSum 1 (2 * t) b p = c :=
  monic_even_eventually_const' t b
end QuadraticFloor
