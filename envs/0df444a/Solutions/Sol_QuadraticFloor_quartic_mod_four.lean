-- Prove2me | solution 1 for QuadraticFloor.quartic_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:14.814839+00:00
-- url     : https://prove2.me/submissions/bb0c4fb6-0454-4005-8f40-fc37c9a63c41

module
public import Definitions.Def_QuadraticFloor
public import Definitions.Def_QuadraticFloor_Solution
public import Theorems.Thm_P2M_QuadraticFloor_quartic_mod_four__76299dd4b54b


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ∃ m : ℤ, (bern (40 * p) (Theta p)).re = m ∧ m ≡ 2 * (zB 1 p - zB 3 p) [ZMOD 4] :=
  quartic_mod_four' hp2 hp5
end QuadraticFloor
