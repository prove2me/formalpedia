-- Prove2me | solution 1 for QuadraticFloor.kap_neg_one_mul_legendre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:33.545908+00:00
-- url     : https://prove2.me/submissions/a146dc95-bbae-46cb-b202-df296ed1454d

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) : kap p (-1) * legendreSym p (-1) = -1 := by
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_eq_if_mod_four]
  have hodd := odd_of_ne_two hp2
  have h2 : p % 2 = 1 := Nat.odd_iff.1 hodd
  unfold kap
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h | h
  · simp only [h, ite_true, show p % 2 ≠ 0 by omega, ite_false]; decide
  · simp only [h, show (3 : ℕ) ≠ 1 by decide, ite_false, show p % 2 ≠ 0 by omega]; decide
end QuadraticFloor
