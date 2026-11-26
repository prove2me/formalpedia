-- Prove2me | solution 1 for QuadraticFloor.eta_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:59.416894+00:00
-- url     : https://prove2.me/submissions/e83812b1-294b-46c6-9c13-3aca524d7120

module
public import Definitions.Def_QuadraticFloor_RootCount
public import Definitions.Def_QuadraticFloor_Eta
public import Theorems.Thm_P2M_QuadraticFloor_eta_eq__74b5fa8b45c2

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) {x : ℕ} (hx : p ∣ x) : eta p x = 0 := by
  rw [eta_eq' hp2, (legendreSym.eq_zero_iff p _).2, mul_zero]
  exact_mod_cast (ZMod.natCast_eq_zero_iff x p).2 hx
end QuadraticFloor
