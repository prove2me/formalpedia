-- Prove2me | solution 1 for QuadraticFloor.periodic_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:27.234171+00:00
-- url     : https://prove2.me/submissions/b4b5c28c-09b0-4117-8040-7ca9cf696bec

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace QuadraticFloor
theorem _root_.solution {g : ℤ → ℤ} (hg : ∀ m, g (m + p) = g m) (m k : ℤ) : g (m + p * k) = g m := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih => rw [show m + p * ((i : ℤ) + 1) = (m + p * i) + p by ring, hg, ih]
  | pred i ih =>
    rw [← ih, show m + p * (-(i : ℤ)) = (m + p * (-(i : ℤ) - 1)) + p by ring, hg]
end QuadraticFloor
